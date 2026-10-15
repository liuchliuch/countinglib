#!/usr/bin/env python3
"""Check the curated English public documentation without running Lean."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import sys
import tomllib
from urllib.parse import unquote, urlsplit

DOCS = (
    'README.md', 'CONTRIBUTING.md', 'PROVENANCE.md', 'LICENSE.md',
    'docs/getting-started.md', 'docs/architecture.md', 'docs/api.md',
    'docs/algorithms.md', 'docs/flagships.md', 'docs/coverage.md',
    'docs/verification.md', 'docs/roadmap.md', 'docs/release.md',
    'docs/reference.md',
    'docs/references.md', 'docs/api-site.md', 'docs/continuous-integration.md',
)
EXAMPLES = ('RelationalCounting', 'GraphReduction', 'Interpolation',
            'Holant', 'ComplexCSP', 'PlanarHom', 'MatchgateWidth')
CJK = re.compile(r'[\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff]')
LINK = re.compile(r'!?\[[^\]\n]*\]\(([^)\n]+)\)')


def check(root: Path) -> dict:
    root = root.resolve()
    errors, links, words = [], 0, {}
    for rel in DOCS:
        p = root / rel
        if not p.is_file():
            errors.append(f'Missing public document: {rel}')
            continue
        value = p.read_text()
        words[rel] = len(value.split())
        if CJK.search(value):
            errors.append(f'Non-English prose in public document: {rel}')
        limit = 650 if rel == 'README.md' else 900
        if words[rel] > limit:
            errors.append(f'Public document exceeds {limit} words: {rel}')
        if not value.startswith('# '):
            errors.append(f'Missing document title: {rel}')
        fence = None
        for line in value.splitlines():
            if line.startswith('```'):
                fence = None if fence is not None else line[3:].strip()
        if fence is not None:
            errors.append(f'Unclosed code fence: {rel}')
        for target in LINK.findall(value):
            target = target.strip().split(' "', 1)[0].strip('<>')
            parsed = urlsplit(target)
            if parsed.scheme or parsed.netloc or not parsed.path:
                continue
            path = (p.parent / unquote(parsed.path)).resolve()
            links += 1
            if not path.is_relative_to(root) or not path.exists():
                errors.append(f'Broken local link: {rel} -> {target}')
    for name in EXAMPLES:
        p = root / f'docs/examples/{name}.lean'
        if not p.is_file():
            errors.append(f'Missing tutorial: {name}')
        elif CJK.search(p.read_text()):
            errors.append(f'Non-English tutorial comment: {name}')
    readme = (root / 'README.md').read_text() if (root / 'README.md').is_file() else ''
    if not readme.startswith('# CountingLib\n'):
        errors.append('README must use the CountingLib project name')
    lean = (root / 'lean-toolchain').read_text().strip().split(':')[-1].removeprefix('v')
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')['rev']
    if f'Lean {lean}' not in readme or mathlib not in readme:
        errors.append('README dependency versions differ from the committed locks')
    config = tomllib.loads((root / 'lakefile.toml').read_text())
    if config['name'] != 'countingComplexity':
        errors.append('Public usage assumes the unchanged countingComplexity Lake package')
    return dict(status='passed' if not errors else 'failed',
                scope='English public prose, links, limits, tutorial presence, branding and lock consistency; not Lean elaboration or proof acceptance.',
                documents=len(DOCS), local_links_checked=links, word_counts=words, errors=errors)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    try:
        result = check(args.root)
    except (OSError, ValueError, KeyError, StopIteration) as error:
        print(f'Public documentation check failed: {error}', file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0 if result['status'] == 'passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
