#!/usr/bin/env python3
"""Build or check the selected public API browser, using Python's standard library."""
from __future__ import annotations

import argparse
import hashlib
import html
import json
from pathlib import Path
import re
import sys
from urllib.parse import quote

REPOSITORY = 'https://github.com/liuchliuch/countinglib'
CATALOGS = (
    ('tools', 'projects/reuse-catalog/data/tool-index.json',
     'projects/reuse-catalog/data/exported-types.jsonl'),
    ('flagships', 'projects/reuse-contracts/data/flagship-index.json',
     'projects/reuse-contracts/data/exported-types.jsonl'),
    ('core', 'data/api/core-index.json', 'data/api/core-types.jsonl'),
)
READABLE_TYPES = 'data/api/readable-types.jsonl'
SCOPE = ('Selected public interfaces: foundations, algorithms, intermediate tools, and four flagship directions. '
         'This is not the complete declaration reference. Full elaborated types are '
         'rendered from the recorded Lean environment exports; this site is not a proof certificate.')
CONTRACT_FIELDS = (
    ('fixed_parameters', 'Fixed parameters'), ('runtime_inputs', 'Runtime inputs'),
    ('promises', 'Promises'), ('input_promises', 'Input promises'),
    ('outputs', 'Outputs'), ('resources', 'Resources'),
    ('auxiliary_resources', 'Auxiliary resources'),
    ('reduction_direction_and_type', 'Reduction'), ('direction', 'Direction'),
    ('cost', 'Cost'), ('limits', 'Limits'), ('nontrivial_examples', 'Examples'),
)


def sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def json_bytes(value: object, *, pretty: bool = False) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                       indent=2 if pretty else None,
                       separators=None if pretty else (',', ':')) + '\n').encode('utf-8')


def source_url(version: str, path: str, line: int | None = None) -> str:
    target = f'{REPOSITORY}/blob/{quote(version, safe="")}/{quote(path, safe="/")}'
    return target + (f'#L{line}' if line else '')


def read_json(path: Path) -> object:
    return json.loads(path.read_text(encoding='utf-8'))


def confined_file(root: Path, relative: str) -> Path:
    path = root / relative
    if not path.resolve().is_relative_to(root.resolve()) or not path.is_file():
        raise ValueError(f'Missing or external source: {relative}')
    return path


def load_catalog(root: Path, version: str) -> dict:
    """Preserve actual exported types; fail if source or catalog evidence drifts."""
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._-]*', version):
        raise ValueError('Version must be a tag or branch containing letters, digits, dot, dash, or underscore')
    families, declarations, inputs, sources, names = [], [], [], {}, set()
    actual_types = {}
    toolchain_path = confined_file(root, 'lean-toolchain')
    toolchain = toolchain_path.read_text(encoding='utf-8').strip()
    if toolchain != 'leanprover/lean4:v4.34.1':
        raise ValueError('The API exports require the pinned Lean 4.34.1 toolchain')
    inputs.append({'path': 'lean-toolchain', 'sha256': sha256(toolchain_path.read_bytes())})
    for category, index_path, export_path in CATALOGS:
        for relative in (index_path, export_path):
            raw = confined_file(root, relative).read_bytes()
            inputs.append({'path': relative, 'sha256': sha256(raw)})
        catalog = read_json(root / index_path)
        exports = {}
        for line in (root / export_path).read_text(encoding='utf-8').splitlines():
            if not line.strip():
                continue
            item = json.loads(line)
            if item['name'] in exports:
                raise ValueError(f'Duplicate exported type: {item["name"]}')
            exports[item['name']] = item
        family_ids = set()
        for item in catalog['contracts']:
            if item['id'] in family_ids or any(f['id'] == item['id'] for f in families):
                raise ValueError(f'Duplicate contract family: {item["id"]}')
            family_ids.add(item['id'])
            family = {
                'id': item['id'], 'title': item['title'], 'category': category,
                'fields': [{'label': label, 'text': item[key]}
                           for key, label in CONTRACT_FIELDS if item.get(key)],
            }
            if item.get('public_import'):
                family['public_import'] = item['public_import']
            provenance = item.get('source_version', {})
            if provenance:
                family['paper_note'] = provenance['paper'].replace(
                    '; use release commit rather than inventing arXiv/version label',
                    '; the contract follows the manuscript bundled with the pinned Lean source')
                match = re.search(r'arXiv:(\d{4}\.\d{4,5}(?:v\d+)?)', provenance['paper'])
                if match:
                    family['paper_url'] = 'https://arxiv.org/abs/' + match[1]
                if provenance.get('repository') and provenance.get('commit'):
                    if not re.fullmatch(r'https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', provenance['repository']) or not re.fullmatch(r'[0-9a-f]{40}', provenance['commit']):
                        raise ValueError(f'Original source is not a pinned GitHub commit: {item["id"]}')
                    family['original_source_url'] = provenance['repository'] + '/tree/' + provenance['commit']
                family['reference_url'] = source_url(version, 'docs/references.md')
            families.append(family)
        for item in catalog['declarations']:
            name = item['name']
            if name in names:
                raise ValueError(f'Duplicate declaration: {name}')
            names.add(name)
            exported = exports.get(name)
            if not exported or exported.get('type_pp_all') != item.get('type_pp_all'):
                raise ValueError(f'Elaborated type disagrees with export: {name}')
            actual_types[name] = exported
            if not isinstance(item['type_pp_all'], str) or not item['type_pp_all'].strip():
                raise ValueError(f'Empty elaborated type: {name}')
            if exported.get('type') != item.get('full_type', item.get('type')):
                raise ValueError(f'Lean expression disagrees with export: {name}')
            for body_key in ('specification_body', 'specification_body_pp_all'):
                if item.get(body_key) != exported.get(body_key):
                    raise ValueError(f'Specification body disagrees with export: {name}')
            if item['contract_family'] not in family_ids:
                raise ValueError(f'Unknown contract family: {name}')
            provider = item.get('provider', item)
            relative = provider['source_path']
            path = confined_file(root, relative)
            if relative not in sources:
                sources[relative] = sha256(path.read_bytes())
            if sources[relative] != provider['source_sha256']:
                raise ValueError(f'Source changed since catalog extraction: {relative}')
            line = provider['source_line']
            if not isinstance(line, int) or not 1 <= line <= len(path.read_text(encoding='utf-8').splitlines()):
                raise ValueError(f'Invalid source line: {name}')
            module = provider.get('module', item.get('provider_module'))
            if module != exported['module']:
                raise ValueError(f'Provider module disagrees with export: {name}')
            row = {
                'name': name, 'display_name': item.get('public_spelling', name),
                'family': item['contract_family'], 'category': category,
                'module': module, 'import': item.get('entry', item.get('direct_import', module)),
                'kind': item.get('declaration_kind', item['role']), 'role': item['role'],
                'type': item['type_pp_all'], 'source_url': source_url(version, relative, line),
                'source_path': relative, 'source_line': line, 'source_sha256': sources[relative],
            }
            if exported.get('type_pp') and item.get('type_pp') == exported['type_pp']:
                row['readable_type'] = exported['type_pp']
            if item.get('summary'):
                row['summary'] = item['summary']
            if item.get('public_name_semantics'):
                row['name_semantics'] = item['public_name_semantics']
            if item.get('original_declaration'):
                row['original_declaration'] = item['original_declaration']
            if item.get('paper_item'):
                row['paper_item'] = item['paper_item']
            if item.get('specification_body_pp_all'):
                row['specification'] = item['specification_body_pp_all']
            declarations.append(row)
        if set(exports) != {i['name'] for i in catalog['declarations']}:
            raise ValueError(f'Export/catalog declaration sets differ: {index_path}')
    raw = confined_file(root, READABLE_TYPES).read_bytes()
    inputs.append({'path': READABLE_TYPES, 'sha256': sha256(raw)})
    readable = {}
    for line in raw.decode('utf-8').splitlines():
        if not line.strip():
            continue
        item = json.loads(line)
        if item['name'] in readable:
            raise ValueError(f'Duplicate readable type: {item["name"]}')
        readable[item['name']] = item
    expected = {row['name'] for row in declarations if row['category'] != 'core'}
    if set(readable) != expected:
        raise ValueError('Readable type selection does not match the tool and flagship catalogs')
    for row in declarations:
        if row['name'] not in readable:
            continue
        pretty = readable[row['name']]
        actual = actual_types[row['name']]
        if pretty.get('type') != actual['type'] or pretty.get('module') != actual['module']:
            raise ValueError(f'Readable type expression disagrees with export: {row["name"]}')
        if not isinstance(pretty.get('type_pp'), str) or not pretty['type_pp'].strip():
            raise ValueError(f'Empty readable type: {row["name"]}')
        row['readable_type'] = pretty['type_pp']
    return {
        'schema_version': 1, 'version': version, 'repository': REPOSITORY, 'scope': SCOPE,
        'families': sorted(families, key=lambda x: (x['category'], x['title'])),
        'declarations': sorted(declarations, key=lambda x: (x['display_name'], x['name'])),
        'inputs': sorted(inputs, key=lambda x: x['path']),
        'source_files_checked': len(sources),
    }


def build_files(root: Path, version: str, templates: Path) -> dict[str, bytes]:
    data = load_catalog(root, version)
    replacements = {
        '@@VERSION@@': html.escape(version),
        '@@SOURCE_BASE@@': source_url(version, ''),
        '@@COUNT@@': str(len(data['declarations'])),
        '@@MODULES@@': str(len({d['module'] for d in data['declarations']})),
    }
    index = (templates / 'index.html').read_text(encoding='utf-8')
    for key, value in replacements.items():
        index = index.replace(key, value)
    outputs = {'index.html': index.encode('utf-8'), 'api-data.json': json_bytes(data),
               'app.js': (templates / 'app.js').read_bytes(),
               'style.css': (templates / 'style.css').read_bytes(), '.nojekyll': b''}
    manifest = {
        'schema_version': 1, 'version': version, 'scope': SCOPE,
        'declarations': len(data['declarations']), 'contract_families': len(data['families']),
        'modules': len({d['module'] for d in data['declarations']}),
        'source_files_checked': data['source_files_checked'], 'inputs': data['inputs'],
        'outputs': [{'path': name, 'sha256': sha256(value)} for name, value in sorted(outputs.items())],
    }
    outputs['manifest.json'] = json_bytes(manifest, pretty=True)
    return outputs


def write_or_check(output: Path, files: dict[str, bytes], check: bool) -> list[str]:
    errors = []
    if check:
        for name, value in files.items():
            path = output / name
            if not path.is_file() or path.read_bytes() != value:
                errors.append(f'Stale or missing generated API asset: {path}')
        if output.is_dir():
            for path in sorted(output.rglob('*')):
                if path.is_file() and path.relative_to(output).as_posix() not in files:
                    errors.append(f'Unexpected generated API asset: {path}')
    else:
        output.mkdir(parents=True, exist_ok=True)
        for name, value in files.items():
            (output / name).write_bytes(value)
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path, help='Default: <root>/docs/api')
    parser.add_argument('--version', default='v0.1.1', help='Source-link tag or branch')
    parser.add_argument('--check', action='store_true', help='Fail on stale assets without writing')
    args = parser.parse_args()
    try:
        files = build_files(args.root, args.version, Path(__file__).resolve().parent / 'api_site')
        errors = write_or_check(args.output or args.root / 'docs/api', files, args.check)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f'API site generation failed: {error}', file=sys.stderr)
        return 1
    for error in errors:
        print(error, file=sys.stderr)
    if errors:
        return 1
    manifest = json.loads(files['manifest.json'])
    print(json.dumps({'status': 'passed', 'mode': 'check' if args.check else 'build',
                      **{k: manifest[k] for k in ('version', 'declarations', 'modules', 'contract_families', 'source_files_checked')}}, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
