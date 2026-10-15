"""Installation boundary regressions; these tests do not run Git, Lake, or Lean."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

MODULE_PATH = Path(__file__).resolve().parents[1] / 'scripts/check_downstream.py'
SPEC = importlib.util.spec_from_file_location('check_downstream', MODULE_PATH)
downstream = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(downstream)
REVISION = 'a' * 40
URL = 'https://github.com/liuchliuch/countinglib'


class InstallationBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.source = self.base / 'library'
        self.consumer = self.base / 'consumer'
        self.source.mkdir()
        (self.source / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
        (self.source / 'lake-manifest.json').write_text(json.dumps({'packages': [
            {'name': 'component', 'type': 'path', 'dir': 'projects/component'},
            {'name': 'mathlib', 'type': 'git', 'url': 'https://github.com/leanprover-community/mathlib4',
             'rev': 'b' * 40, 'subDir': None}]}))
        component = self.source / 'projects/component'
        component.mkdir(parents=True)
        (component / 'lake-manifest.json').write_text(json.dumps({'packages': [
            {'name': 'mathlib', 'type': 'git', 'url': 'https://github.com/leanprover-community/mathlib4',
             'rev': 'b' * 40, 'subDir': None}]}))
        self.manifest = {'packages': [
            {'name': 'countingComplexity', 'type': 'git', 'url': URL, 'rev': REVISION,
             'inputRev': REVISION, 'subDir': None, 'inherited': False},
            {'name': 'component', 'type': 'path', 'dir': '.lake/packages/countingComplexity/projects/component',
             'inherited': True},
            {'name': 'mathlib', 'type': 'git', 'url': 'https://github.com/leanprover-community/mathlib4',
             'rev': 'b' * 40, 'subDir': None}]}

    def validate(self, manifest=None):
        return downstream.validate_manifest(manifest or self.manifest, self.consumer, self.source, URL, REVISION)

    def test_git_requirement_and_exact_component_layout(self):
        receipt = downstream.prepare(self.source, self.consumer, URL + '.git', REVISION, 'core')
        import tomllib
        config = tomllib.loads((self.consumer / 'lakefile.toml').read_text())
        self.assertEqual(config['require'], [{'name': 'countingComplexity', 'git': URL, 'rev': REVISION}])
        self.assertEqual(receipt['status'], 'prepared')
        local, external = self.validate()
        self.assertEqual(local, {'component': Path('projects/component')})
        self.assertEqual(external['mathlib'][1], 'b' * 40)
        with self.assertRaises(FileExistsError):
            downstream.prepare(self.source, self.consumer, URL, REVISION, 'core')

    def test_path_dependency_cannot_pass_as_installation(self):
        self.manifest['packages'][0] = {'name': 'countingComplexity', 'type': 'path', 'dir': str(self.source)}
        with self.assertRaisesRegex(ValueError, 'Git dependency'):
            self.validate()

    def test_changed_commit_tag_and_external_lock_rejected(self):
        for index, key, value in [(0, 'rev', 'c' * 40), (0, 'inputRev', 'main'),
                                  (2, 'rev', 'c' * 40), (2, 'url', 'https://github.com/other/mathlib4')]:
            with self.subTest(index=index, key=key):
                modified = copy.deepcopy(self.manifest)
                modified['packages'][index][key] = value
                with self.assertRaises(ValueError):
                    self.validate(modified)

    def test_conflicting_component_lock_rejected_before_generation(self):
        path = self.source / 'projects/component/lake-manifest.json'
        manifest = json.loads(path.read_text())
        manifest['packages'][0]['rev'] = 'c' * 40
        path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, 'Conflicting Git lock'):
            downstream.prepare(self.source, self.consumer, URL, REVISION, 'core')
        self.assertFalse(self.consumer.exists())

    def test_component_must_live_in_cloned_package(self):
        for value in ['../library/projects/component', '/tmp/component', '.lake/packages/elsewhere/projects/component']:
            self.manifest['packages'][1]['dir'] = value
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, 'escapes'):
                self.validate()

    def test_missing_extra_and_duplicate_providers_rejected(self):
        for packages in [self.manifest['packages'][:-1],
                         self.manifest['packages'] + [{'name': 'foreign', 'type': 'path', 'dir': '/tmp'}],
                         self.manifest['packages'] + [self.manifest['packages'][0]]]:
            with self.subTest(packages=packages), self.assertRaises(ValueError):
                self.validate({'packages': packages})

    def test_invalid_input_creates_no_consumer(self):
        for revision, url in [('main', URL), (REVISION, 'https://token@github.com/owner/repo'),
                              (REVISION, 'file:///tmp/repository'), (REVISION, URL + '?token=secret')]:
            with self.subTest(revision=revision, url=url), self.assertRaises(ValueError):
                downstream.prepare(self.source, self.consumer, url, revision, 'core')
            self.assertFalse(self.consumer.exists())

    def test_readme_and_tutorial_sources_come_from_clone(self):
        self.consumer.mkdir()
        examples = self.source / 'docs/examples'
        examples.mkdir(parents=True)
        for name in downstream.CORE_EXAMPLES + downstream.FLAGSHIP_EXAMPLES:
            (examples / f'{name}.lean').write_text(f'import Counting\n-- {name}\n')
        (self.source / 'README.md').write_text('```lean\nimport Counting\n#check Nat\n```\n')
        clients = downstream.client_sources(self.source, self.consumer, 'all')
        self.assertEqual(len(clients), 9)  # aggregate + seven tutorials + README
        self.assertFalse((self.consumer / '.lake/build').exists())
        for name in downstream.CORE_EXAMPLES + downstream.FLAGSHIP_EXAMPLES:
            self.assertEqual((examples / f'{name}.lean').read_bytes(),
                             (self.consumer / f'CountingLibConsumer/{name}.lean').read_bytes())

    def test_cli_prepare_does_not_claim_passed(self):
        self.assertEqual(downstream.main(['--source', str(self.source), '--work-dir', str(self.consumer),
                                        '--revision', REVISION, '--prepare-only']), 0)
        receipt = json.loads((self.consumer / 'result.json').read_text())
        self.assertEqual(receipt['status'], 'prepared')
        self.assertEqual(receipt['commands'], [])
        self.assertEqual(downstream.main(['--source', str(self.source), '--work-dir', str(self.consumer),
                                        '--revision', REVISION, '--prepare-only']), 1)
        self.assertEqual(json.loads((self.consumer / 'result.json').read_text()), receipt)


if __name__ == '__main__':
    unittest.main()
