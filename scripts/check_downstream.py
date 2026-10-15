#!/usr/bin/env python3
"""Compile fresh clients against an exact public Git dependency, not a path dependency.

Only explicit cache flags reuse local artifacts. The generated client is always new.
A failed attempt keeps its directory, commands, logs, and JSON receipt.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import platform
import shutil
import subprocess
import sys
import time
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parents[1]
CORE_EXAMPLES = ('RelationalCounting', 'GraphReduction', 'Interpolation')
FLAGSHIP_EXAMPLES = ('Holant', 'ComplexCSP', 'PlanarHom', 'MatchgateWidth')
SHA = re.compile(r'[0-9a-f]{40}\Z')


def now():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def environment():
    env = os.environ.copy()
    fallback = Path.home() / '.cache/codex-runtimes/codex-primary-runtime/dependencies/bin/fallback'
    parts = [str(Path.home() / '.elan/bin')]
    if (fallback / 'git').is_file():
        parts.insert(0, str(fallback))
    env['PATH'] = os.pathsep.join(parts + [env.get('PATH', '')])
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    env['GIT_TERMINAL_PROMPT'] = '0'
    return env


def repository_url(value):
    parsed = urlparse(value)
    if parsed.scheme != 'https' or not parsed.netloc or parsed.username or parsed.password:
        raise ValueError('Repository must be an HTTPS URL without embedded credentials')
    if parsed.query or parsed.fragment or not parsed.path.strip('/'):
        raise ValueError('Repository URL must have a path and no query or fragment')
    return value.rstrip('/').removesuffix('.git')


def package_index(manifest):
    packages = manifest.get('packages')
    if not isinstance(packages, list):
        raise ValueError('Manifest has no packages list')
    result = {}
    for item in packages:
        name = item.get('name')
        if not isinstance(name, str) or name in result:
            raise ValueError('Missing or duplicate package name')
        result[name] = item
    return result


def git_identity(item):
    if item.get('type') != 'git' or not SHA.fullmatch(item.get('rev', '')):
        raise ValueError('Git dependency is not locked to a full commit')
    return (repository_url(item['url']), item['rev'], item.get('subDir'))


def layout(source):
    root = package_index(json.loads((source / 'lake-manifest.json').read_text()))
    local = {}
    for name, item in root.items():
        if item.get('type') == 'git':
            git_identity(item)
            continue
        if item.get('type') != 'path':
            raise ValueError('Expected local path components or locked Git dependencies')
        path = Path(item['dir'])
        if path.is_absolute() or '..' in path.parts or not path.parts or path.parts[0] != 'projects':
            raise ValueError('Local component must stay inside projects/')
        local[name] = path
    external = {}
    for path in [Path('.'), *local.values()]:
        for name, item in package_index(json.loads((source / path / 'lake-manifest.json').read_text())).items():
            if item.get('type') == 'git':
                identity = git_identity(item)
                if name in external and external[name] != identity:
                    raise ValueError(f'Conflicting Git lock for {name}')
                external[name] = identity
    if set(local) & set(external) or 'countingComplexity' in (set(local) | set(external)):
        raise ValueError('Local and external package providers overlap')
    return local, external


def validate_manifest(manifest, consumer, source, repository, revision):
    """Reject a path fallback, a moved commit, foreign packages, or changed locks."""
    packages = package_index(manifest)
    local, external = layout(source)
    if set(packages) != set(local) | set(external) | {'countingComplexity'}:
        raise ValueError('Downstream package set differs from the library layout')
    library = packages['countingComplexity']
    if git_identity(library) != (repository_url(repository), revision, None):
        raise ValueError('Downstream library is not the requested exact Git commit')
    if library.get('inputRev') != revision or library.get('inherited') is not False:
        raise ValueError('Downstream must directly require the tested commit')
    checkout = consumer / '.lake/packages/countingComplexity'
    for name, path in local.items():
        entry = packages[name]
        if entry.get('type') != 'path' or entry.get('inherited') is not True:
            raise ValueError(f'Component {name} is not inherited from the Git package')
        if (consumer / entry['dir']).resolve() != (checkout / path).resolve():
            raise ValueError(f'Component {name} escapes the Git checkout')
    for name, identity in external.items():
        if git_identity(packages[name]) != identity:
            raise ValueError(f'External dependency lock changed: {name}')
    return local, external


def prepare(source, consumer, repository, revision, tier):
    if not SHA.fullmatch(revision):
        raise ValueError('Revision must be a full 40-character lowercase Git commit')
    repository = repository_url(repository)
    layout(source)  # Fail before creating an output directory if locks are malformed.
    toolchain = (source / 'lean-toolchain').read_text()
    if toolchain.strip() != 'leanprover/lean4:v4.34.1':
        raise ValueError('Expected the fixed Lean 4.34.1 toolchain')
    consumer.mkdir(parents=True, exist_ok=False)
    (consumer / 'lean-toolchain').write_text(toolchain)
    (consumer / 'lakefile.toml').write_text(
        'name = "countingLibConsumer"\ndefaultTargets = ["CountingLibConsumer"]\n\n'
        '[[require]]\nname = "countingComplexity"\n'
        f'git = {json.dumps(repository)}\nrev = {json.dumps(revision)}\n\n'
        '[[lean_lib]]\nname = "CountingLibConsumer"\n')
    return {'schema_version': 1, 'status': 'prepared', 'started_utc': now(),
            'repository': repository, 'revision': revision, 'tier': tier,
            'consumer': str(consumer), 'commands': [], 'cache_links': [],
            'scope': 'Fresh downstream clients against a Git SHA; not a full source audit or a cold-build claim'}


def run(command, cwd, log, env, receipt):
    started = time.monotonic()
    record = {'command': command, 'cwd': str(cwd), 'log': log.name}
    receipt['commands'].append(record)
    with log.open('w') as stream:
        process = subprocess.run(command, cwd=cwd, env=env, stdout=stream, stderr=subprocess.STDOUT)
    record.update(exit_code=process.returncode, elapsed_seconds=time.monotonic() - started,
                  log_sha256=digest(log))
    if process.returncode:
        raise RuntimeError(f'{command[0]} failed ({process.returncode}); see {log}')


def git_output(directory, *args, env):
    return subprocess.check_output(['git', '-C', str(directory), *args], env=env, text=True).strip()


def link_external_cache(source, consumer, receipt, env):
    _, external = layout(source)
    target = consumer / '.lake/packages'
    target.mkdir(parents=True, exist_ok=True)
    for name, identity in sorted(external.items()):
        origin = source / '.lake/packages' / name
        if git_output(origin, 'rev-parse', 'HEAD', env=env) != identity[1]:
            raise ValueError(f'Cache checkout has the wrong commit: {name}')
        actual = repository_url(git_output(origin, 'remote', 'get-url', 'origin', env=env))
        if actual != identity[0]:
            raise ValueError(f'Cache checkout has the wrong remote: {name}')
        (target / name).symlink_to(origin.resolve(), target_is_directory=True)
        receipt['cache_links'].append({'kind': 'external', 'package': name, 'path': str(origin.resolve()), 'commit': identity[1]})


def copy_project_builds(source, checkout, receipt, env):
    # Cache reuse is explicit and accepted only for identical committed proof/config inputs.
    if git_output(source, 'rev-parse', 'HEAD', env=env) != receipt['revision']:
        raise ValueError('Project-cache source is not the tested commit')
    local, _ = layout(source)
    for path in [Path('.'), *local.values()]:
        for pattern in ('*.lean', 'lakefile.*', 'lake-manifest.json', 'lean-toolchain'):
            for item in (checkout / path).rglob(pattern):
                if '.lake' in item.relative_to(checkout / path).parts:
                    continue
                counterpart = source / item.relative_to(checkout)
                if not counterpart.is_file() or digest(item) != digest(counterpart):
                    raise ValueError(f'Project-cache source differs: {item.relative_to(checkout)}')
        origin = source / path / '.lake/build'
        if origin.is_dir():
            target = checkout / path / '.lake/build'
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.exists() or target.is_symlink():
                raise ValueError(f'Project build output already exists: {target}')
            command = (['cp', '-cR'] if platform.system() == 'Darwin' else ['cp', '--reflink=auto', '-R'])
            command += [str(origin.resolve()), str(target)]
            run(command, checkout, Path(receipt['consumer']) / f'copy-build-{len(receipt["cache_links"])}.log', env, receipt)
            receipt['cache_links'].append({'kind': 'project-build-copy', 'package_path': str(path), 'path': str(origin.resolve())})


def client_sources(checkout, consumer, tier):
    examples = CORE_EXAMPLES + (FLAGSHIP_EXAMPLES if tier == 'all' else ())
    module_dir = consumer / 'CountingLibConsumer'
    module_dir.mkdir()
    for name in examples:
        shutil.copyfile(checkout / f'docs/examples/{name}.lean', module_dir / f'{name}.lean')
    snippets = re.findall(r'```lean\s*\n(.*?)\n```', (checkout / 'README.md').read_text(), re.DOTALL)
    if not snippets:
        raise ValueError('README must contain a Lean client')
    imports = '\n'.join(f'import CountingLibConsumer.{name}' for name in examples)
    # Keep each README snippet in its own module; imports must precede declarations.
    readme_modules = []
    for index, text in enumerate(snippets, 1):
        name = f'Readme{index}'
        (module_dir / f'{name}.lean').write_text(text + '\n')
        readme_modules.append(name)
    imports += ''.join(f'\nimport CountingLibConsumer.{name}' for name in readme_modules)
    (consumer / 'CountingLibConsumer.lean').write_text(imports + '\n')
    return [Path('CountingLibConsumer.lean'),
            *(Path('CountingLibConsumer') / f'{name}.lean' for name in (*examples, *readme_modules))]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=ROOT)
    parser.add_argument('--repository', default='https://github.com/liuchliuch/countinglib')
    parser.add_argument('--revision', required=True)
    parser.add_argument('--work-dir', type=Path, required=True, help='New directory; never reused or overwritten')
    parser.add_argument('--tier', choices=('core', 'all'), default='core')
    parser.add_argument('--reuse-external-cache', action='store_true', help='Link only exact locked external checkouts from --source')
    parser.add_argument('--copy-checkout-builds', action='store_true', help='Explicitly copy matching library build caches; source outputs stay isolated and clients remain fresh')
    parser.add_argument('--prepare-only', action='store_true', help='Generate configuration without running Git or Lake; not a passing installation test')
    args = parser.parse_args(argv)
    source, consumer = args.source.resolve(), args.work_dir.absolute()
    receipt = None
    try:
        receipt = prepare(source, consumer, args.repository, args.revision, args.tier)
        save(consumer / 'result.json', receipt)
        if args.prepare_only:
            return 0
        receipt['status'] = 'running'
        env = environment()
        if args.reuse_external_cache:
            link_external_cache(source, consumer, receipt, env)
        run(['lake', 'update'], consumer, consumer / 'update.log', env, receipt)
        manifest = consumer / 'lake-manifest.json'
        checkout = consumer / '.lake/packages/countingComplexity'
        validate_manifest(json.loads(manifest.read_text()), consumer, source, args.repository, args.revision)
        if git_output(checkout, 'rev-parse', 'HEAD', env=env) != args.revision:
            raise ValueError('Resolved checkout does not match the requested commit')
        if (checkout / 'lean-toolchain').read_bytes() != (source / 'lean-toolchain').read_bytes():
            raise ValueError('Resolved library toolchain differs from the source checkout')
        receipt['manifest_sha256'] = digest(manifest)
        if args.copy_checkout_builds:
            copy_project_builds(source, checkout, receipt, env)
        clients = client_sources(checkout, consumer, args.tier)
        receipt['client_sources'] = {str(p): digest(consumer / p) for p in clients}
        run(['lake', 'exe', 'cache', 'get'], consumer, consumer / 'external-cache.log', env, receipt)
        run(['lake', 'build'], consumer, consumer / 'build.log', env, receipt)
        for path in clients:
            artifact = consumer / '.lake/build/lib/lean' / path.with_suffix('.olean')
            if not artifact.is_file():
                raise ValueError(f'Fresh client artifact missing: {artifact}')
        if digest(manifest) != receipt['manifest_sha256']:
            raise ValueError('Downstream dependency manifest changed during compilation')
        if any(digest(consumer / p) != h for p, h in receipt['client_sources'].items()):
            raise ValueError('Client sources changed during compilation')
        receipt.update(status='passed', resolved_commit=args.revision,
                       fresh_client_modules=len(clients), library_sources_cold_built=False)
        return 0
    except (Exception, KeyboardInterrupt) as error:
        if receipt is not None:
            receipt.update(status='failed', error=str(error) or type(error).__name__)
        print(f'Downstream check failed: {error}', file=sys.stderr)
        return 1
    finally:
        if receipt is not None:
            receipt['finished_utc'] = now()
            save(consumer / 'result.json', receipt)
            print(json.dumps({k: receipt[k] for k in ('status', 'revision', 'consumer')}))


if __name__ == '__main__':
    raise SystemExit(main())
