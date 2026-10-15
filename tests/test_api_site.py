"""Regression tests for source-grounded, deterministic static API generation."""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'scripts/build_api_site.py'
SPEC = importlib.util.spec_from_file_location('build_api_site', SCRIPT)
api = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(api)


class ApiSiteTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n', encoding='utf-8')
        self.templates = SCRIPT.parent / 'api_site'
        for category, index_path, export_path in api.CATALOGS:
            relative = f'sources/{category}.lean'
            source = self.root / relative
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text(f'-- {category}\ntheorem sample : True := True.intro\n', encoding='utf-8')
            module, name = f'Counting.{category}', f'Counting.{category}.sample'
            expression = {'format': 'lean-expr-dag-v1', 'nodes': [['const', 'True', []]], 'root': 0}
            exported = {'name': name, 'module': module, 'type_pp_all': 'True', 'type': expression}
            family = {'id': category, 'title': category.title(), 'cost': 'Semantic equality only.'}
            row = {'name': name, 'contract_family': category, 'role': 'theorem',
                   'type_pp_all': 'True', 'type': expression}
            provider = {'source_path': relative, 'source_line': 2,
                        'source_sha256': api.sha256(source.read_bytes())}
            if category == 'tools':
                row['provider'] = {'module': module, **provider}
                row['entry'] = 'Counting.Tools'
                row['full_type'] = row.pop('type')
                row['public_spelling'] = 'Counting.Public.sample'
                row['declaration_kind'] = 'theorem'
            else:
                row.update(provider, provider_module=module, direct_import=module)
                family.update(source_version={'paper': 'arXiv:2610.00081v1',
                    'repository': 'https://github.com/example/original', 'commit': 'a' * 40},
                    public_import='Counting.Flagships.Sample')
            catalog = {'contracts': [family], 'declarations': [row]}
            path = self.root / index_path
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(catalog), encoding='utf-8')
            (self.root / export_path).write_text(json.dumps(exported) + '\n', encoding='utf-8')

        readable = []
        for category, _, export_path in api.CATALOGS:
            if category != 'core':
                record = json.loads((self.root / export_path).read_text())
                readable.append({**record, 'type_pp': 'True'})
        path = self.root / api.READABLE_TYPES
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(''.join(json.dumps(item) + '\n' for item in readable), encoding='utf-8')

    def edit_catalog(self, category, action):
        _, relative, _ = next(item for item in api.CATALOGS if item[0] == category)
        path = self.root / relative
        value = json.loads(path.read_text())
        action(value)
        path.write_text(json.dumps(value), encoding='utf-8')

    def test_preserves_elaborated_types_and_alias_identity(self):
        data = api.load_catalog(self.root, 'v0.1.1')
        self.assertEqual(len(data['declarations']), len(api.CATALOGS))
        row = next(item for item in data['declarations'] if item['category'] == 'tools')
        self.assertEqual(row['name'], 'Counting.tools.sample')
        self.assertEqual(row['display_name'], 'Counting.Public.sample')
        self.assertEqual(row['type'], 'True')
        self.assertEqual(row['import'], 'Counting.Tools')
        self.assertTrue(row['source_url'].endswith('/v0.1.1/sources/tools.lean#L2'))

    def test_paper_version_and_contract_are_preserved(self):
        data = api.load_catalog(self.root, 'v0.1.1')
        family = next(item for item in data['families'] if item['id'] == 'flagships')
        self.assertEqual(family['paper_url'], 'https://arxiv.org/abs/2610.00081v1')
        self.assertEqual(family['original_source_url'], 'https://github.com/example/original/tree/' + 'a' * 40)
        self.assertEqual(family['fields'], [{'label': 'Cost', 'text': 'Semantic equality only.'}])

    def test_deterministic_outputs_and_manifest_hashes(self):
        first = api.build_files(self.root, 'v0.1.1', self.templates)
        second = api.build_files(self.root, 'v0.1.1', self.templates)
        self.assertEqual(first, second)
        self.assertNotIn('@@', first['index.html'].decode())
        manifest = json.loads(first['manifest.json'])
        self.assertEqual(manifest['declarations'], len(api.CATALOGS))
        for record in manifest['outputs']:
            self.assertEqual(api.sha256(first[record['path']]), record['sha256'])

    def test_check_never_repairs_stale_files(self):
        files = api.build_files(self.root, 'v0.1.1', self.templates)
        output = self.root / 'site'
        self.assertEqual(api.write_or_check(output, files, False), [])
        self.assertEqual(api.write_or_check(output, files, True), [])
        (output / 'app.js').write_text('stale', encoding='utf-8')
        self.assertTrue(api.write_or_check(output, files, True))
        self.assertEqual((output / 'app.js').read_text(), 'stale')
        (output / 'stray.txt').write_text('stray', encoding='utf-8')
        self.assertTrue(any('Unexpected' in item for item in api.write_or_check(output, files, True)))

    def test_exports_require_matching_lean_toolchain(self):
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n', encoding='utf-8')
        with self.assertRaisesRegex(ValueError, 'pinned Lean 4.34.1'):
            api.load_catalog(self.root, 'v0.1.1')

    def test_source_drift_is_rejected(self):
        (self.root / 'sources/tools.lean').write_text('-- changed\n', encoding='utf-8')
        with self.assertRaisesRegex(ValueError, 'Source changed'):
            api.load_catalog(self.root, 'v0.1.1')

    def test_type_drift_is_rejected(self):
        self.edit_catalog('tools', lambda value: value['declarations'][0].update(type_pp_all='False'))
        with self.assertRaisesRegex(ValueError, 'type disagrees'):
            api.load_catalog(self.root, 'v0.1.1')

    def test_expression_drift_is_rejected(self):
        self.edit_catalog('tools', lambda value: value['declarations'][0].update(full_type={'different': True}))
        with self.assertRaisesRegex(ValueError, 'expression disagrees'):
            api.load_catalog(self.root, 'v0.1.1')

    def test_specification_body_drift_is_rejected(self):
        self.edit_catalog('tools', lambda value: value['declarations'][0].update(specification_body_pp_all='False'))
        with self.assertRaisesRegex(ValueError, 'Specification body disagrees'):
            api.load_catalog(self.root, 'v0.1.1')

    def test_unknown_family_is_rejected(self):
        self.edit_catalog('tools', lambda value: value['declarations'][0].update(contract_family='missing'))
        with self.assertRaisesRegex(ValueError, 'Unknown contract'):
            api.load_catalog(self.root, 'v0.1.1')

    def test_missing_or_external_source_is_rejected(self):
        self.edit_catalog('tools', lambda value: value['declarations'][0]['provider'].update(source_path='../outside.lean'))
        with self.assertRaisesRegex(ValueError, 'Missing or external'):
            api.load_catalog(self.root, 'v0.1.1')

    def test_source_line_is_checked(self):
        self.edit_catalog('tools', lambda value: value['declarations'][0]['provider'].update(source_line=99))
        with self.assertRaisesRegex(ValueError, 'Invalid source line'):
            api.load_catalog(self.root, 'v0.1.1')

    def test_version_is_a_link_safe_ref(self):
        with self.assertRaisesRegex(ValueError, 'Version must'):
            api.load_catalog(self.root, 'v0.1.1"><script>')

    def test_original_repository_link_must_be_a_pinned_github_commit(self):
        self.edit_catalog('flagships', lambda value: value['contracts'][0]['source_version'].update(repository='javascript:alert(1)'))
        with self.assertRaisesRegex(ValueError, 'pinned GitHub commit'):
            api.load_catalog(self.root, 'v0.1.1')

    def test_readable_type_requires_identical_actual_expression(self):
        path = self.root / api.READABLE_TYPES
        records = [json.loads(line) for line in path.read_text().splitlines()]
        records[0]['type'] = {'different': True}
        path.write_text(''.join(json.dumps(item) + '\n' for item in records), encoding='utf-8')
        with self.assertRaisesRegex(ValueError, 'Readable type expression disagrees'):
            api.load_catalog(self.root, 'v0.1.1')

    def test_signatures_stay_in_json_and_dom_uses_text_nodes(self):
        raw = json.dumps({'type': '</script><img src=x onerror=alert(1)>'})
        decoded = json.loads(raw)
        self.assertIn('</script>', decoded['type'])
        script = (self.templates / 'app.js').read_text()
        self.assertNotIn('innerHTML', script)
        self.assertNotIn('insertAdjacentHTML', script)
        self.assertIn('textContent = text', script)
        index = (self.templates / 'index.html').read_text()
        self.assertNotIn('<script src="http', index)
        self.assertNotIn('api-data.json</script>', index)


if __name__ == '__main__':
    unittest.main()
