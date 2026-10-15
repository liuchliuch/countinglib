#!/usr/bin/env python3
"""Compile and audit CountingLib's public Lean examples.

Use core for the original three examples, all for all seven. This command builds
the directly imported production entry modules, compiles each example into a
fresh private cache directory, then uses Audit.lean
to enumerate its private/generated kernel declarations and their transitive
axioms. Imported library proofs remain under the separate library verification.
All Lake invocations go through scripts/lake. Python 3.11+ is required.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile
import time

CORE = ('RelationalCounting', 'GraphReduction', 'Interpolation')
FLAGSHIPS = ('Holant', 'ComplexCSP', 'PlanarHom', 'MatchgateWidth')
SCOPES = {'core': CORE, 'all': CORE + FLAGSHIPS}


def load_verifier(root: Path):
    path = root / 'scripts/verify.py'
    spec = importlib.util.spec_from_file_location('counting_examples_verify', path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f'Cannot load the verification driver: {path}')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    if module.ROOT != root:
        raise RuntimeError('Verification driver resolved a different project root')
    return module


def source_inventory(root: Path, scope: str, verify) -> list[dict]:
    sources = []
    for name in SCOPES[scope]:
        relative = Path('docs/examples') / (name + '.lean')
        path = root / relative
        if not path.is_file() or path.is_symlink():
            raise RuntimeError(f'Missing or symbolic-link public example: {relative}')
        sources.append({'module': '.'.join(relative.with_suffix('').parts),
                        'path': str(relative), 'sha256': verify.sha(path)})
    return sources


def assert_source_stability(root: Path, sources: list[dict], verify) -> None:
    for source in sources:
        path = root / source['path']
        if not path.is_file() or path.is_symlink() or verify.sha(path) != source['sha256']:
            raise RuntimeError(f'Example source changed during verification: {source["path"]}')


def select_production_inputs(examples: list[dict], production: list[dict], graph: dict,
                             verify) -> list[dict]:
    example_names = {source['module'] for source in examples}
    by_name = {source['module']: source for source in production}
    if example_names & by_name.keys():
        raise RuntimeError('An example module conflicts with a production provider')
    reached = verify.module_closure(sorted(example_names), graph)
    return [by_name[name] for name in sorted(reached & by_name.keys())]


def archive_previous(root: Path, out: Path) -> str | None:
    if not out.exists() or not any(out.iterdir()):
        return None
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    target = root / 'validation/history' / ('examples-' + out.name + '-' + stamp)
    shutil.copytree(out, target)
    return str(target.relative_to(root))


def fingerprint_harness(root: Path, verify) -> dict:
    paths = [Path(__file__).resolve(), root / 'scripts/verify.py', root / 'scripts/lake',
             root / 'validation/Audit.lean', root / 'validation/ImportGraph.lean']
    return {verify.relative(path): verify.sha(path) for path in paths}


def validate_example_audit(prefix: Path, examples: list[dict], artifacts: dict,
                           graph: dict, verify) -> dict:
    audited = verify.validate_audit(prefix, examples, artifacts)
    summary = audited['summary']
    if any(summary.get(key) != 0 for key in ('unsafe_declarations', 'partial_declarations')):
        raise RuntimeError('Public examples contain unsafe or partial declarations')
    closure = {record['name']: record['imports']
               for record in verify.records(Path(str(prefix) + '-closure.jsonl'))}
    for source in examples:
        name = source['module']
        if set(closure[name]) != set(graph[name]):
            raise RuntimeError(f'Compiled example imports differ from parsed source header: {name}')
    return audited


def check(root: Path, scope: str, workers: int, verify, build: bool = True) -> int:
    out = root / 'validation/examples' / scope
    previous = archive_previous(root, out)
    out.mkdir(parents=True, exist_ok=True)
    report = {'schema_version': 1, 'status': 'running', 'profile': scope,
              'started_utc': verify.now(), 'previous_evidence': previous, 'commands': [],
              'workers': workers,
              'scope': 'Fresh tutorial compilation and private/generated kernel declaration/transitive-axiom audit; imported library verification is separate',
              'build_mode': 'Lake prerequisite build with valid incremental artifacts, then fresh example artifacts; existing dependency/toolchain caches are reused; no cold-build claim' if build else 'Fresh example artifacts; prebuilt production, dependency, and toolchain artifacts are reused; no cold-build claim',
              'project_builds_invoked': build}
    started = time.monotonic()
    result = out / 'result.json'
    verify.save_json(result, report)
    try:
        examples = source_inventory(root, scope, verify)
        configs = verify.configurations()
        production, _ = verify.inventory(configs)
        locked = verify.dependencies(configs)
        watched = fingerprint_harness(root, verify)
        report.update(example_modules=len(examples), examples=examples,
                      dependencies=locked, harness_sha256=watched)
        report['installed_dependencies'] = verify.installed_dependencies(locked)
        env = verify.environment(workers)
        version = verify.run([str(verify.LAKE), 'env', 'lean', '--version'],
                             out / 'lean-version.log', env, report['commands']).strip()
        expected = locked['toolchain'].split(':v')[-1]
        if f'version {expected}' not in version:
            raise RuntimeError('Installed Lean version differs from toolchain lock')
        report['lean_version'] = version
        sysroot = Path(verify.run([str(verify.LAKE), 'env', 'lean', '--print-prefix'],
                                 out / 'lean-prefix.log', env, report['commands']).strip())
        toolchain = [sysroot / 'bin' / name for name in ('lean', 'lake', 'leanc')
                     if (sysroot / 'bin' / name).is_file()]
        toolchain_sha = {str(path): verify.sha(path) for path in toolchain}
        report['toolchain_binary_sha256'] = toolchain_sha

        # Lean parses every owned header; no source regex determines dependency
        # reachability. The private audit independently checks compiled imports.
        graph = verify.import_graph(production + examples, 'validation/All.lean',
                                    out, env, report['commands'])
        selected = select_production_inputs(examples, production, graph, verify)
        production_names = {source['module'] for source in production}
        targets = sorted({name for source in examples for name in graph[source['module']]
                          if name in production_names})
        report['prerequisite_entry_modules'] = targets
        if build and targets:
            verify.run([str(verify.LAKE), '--no-cache', '--no-ansi', 'build',
                        *('+' + name for name in targets)], out / 'prerequisites.log',
                       env, report['commands'])
        assert_source_stability(root, examples, verify)
        if verify.configurations() != configs or verify.inventory(configs)[0] != production:
            raise RuntimeError('Production source or package configuration changed during prerequisite build')
        verify.save_json(out / 'production-inputs.json', selected)
        report['imported_production_modules'] = len(selected)
        try:
            artifacts = verify.artifact_map(selected, locked, sysroot)
        except RuntimeError as error:
            raise RuntimeError(f'{error}. First run scripts/verify.py --scope {scope}.') from error
        inputs = verify.hash_artifacts(artifacts, workers)
        verify.save_json(out / 'input-artifact-sha256.json', inputs)

        # The unique directory excludes any previous tutorial olean, so an old
        # successful compile can never substitute for the current source.
        cache_root = root / '.cache/example-checks'
        cache_root.mkdir(parents=True, exist_ok=True)
        cache = Path(tempfile.mkdtemp(prefix=scope + '-', dir=cache_root))
        report['fresh_artifact_directory'] = verify.relative(cache)
        options = configs['countingComplexity'].get('leanOptions', {})
        report['example_lean_options'] = options
        verify.save_json(result, report)
        tutorial_artifacts = {}
        for source in examples:
            name = source['module']
            setup = cache / (name + '-setup.json')
            verify.save_json(setup, {'name': name, 'package?': None,
                'isModule': False, 'imports?': None, 'importArts': artifacts,
                'dynlibs': [], 'plugins': [], 'options': options})
            olean = cache / Path(*name.split('.')).with_suffix('.olean')
            olean.parent.mkdir(parents=True, exist_ok=True)
            verify.run([str(verify.LAKE), 'env', 'lean', '--setup', str(setup),
                        '-o', str(olean), source['path']],
                       out / (Path(source['path']).stem + '.log'), env, report['commands'])
            if not olean.is_file():
                raise RuntimeError(f'Lean did not emit the fresh example artifact: {name}')
            tutorial_artifacts[name] = verify.artifact_entry(olean)
        assert_source_stability(root, examples, verify)
        if verify.hash_artifacts(artifacts, workers) != inputs:
            raise RuntimeError('Imported artifacts changed while examples were compiling')
        artifacts.update(tutorial_artifacts)
        fingerprints = dict(inputs)
        fingerprints.update(verify.hash_artifacts(tutorial_artifacts, workers))
        verify.save_json(out / 'artifact-sha256.json', fingerprints)
        request = out / 'audit-request.json'
        verify.save_json(request, {'modules': [source['module'] for source in examples],
            'all_local_modules': [source['module'] for source in examples],
            'roots': [source['module'] for source in examples],
            'import_artifacts': artifacts})
        request_sha = verify.sha(request)
        prefix = out / 'audit'
        output = verify.run([str(verify.LAKE), 'env', 'lean', '-M24000', '--run',
            'validation/Audit.lean', str(request), str(prefix)], out / 'audit.log',
            env, report['commands'])
        if sum(line.startswith('AUDIT_SUMMARY ') for line in output.splitlines()) != 1:
            raise RuntimeError('Missing unique tutorial audit completion marker')
        audited = validate_example_audit(prefix, examples, artifacts, graph, verify)
        assert_source_stability(root, examples, verify)
        if verify.configurations() != configs or verify.inventory(configs)[0] != production:
            raise RuntimeError('Production source or package configuration changed during tutorial verification')
        if verify.dependencies(configs) != locked or verify.installed_dependencies(locked) != report['installed_dependencies']:
            raise RuntimeError('Dependency state changed during tutorial verification')
        if fingerprint_harness(root, verify) != watched or verify.sha(request) != request_sha:
            raise RuntimeError('Tutorial verification harness or audit request changed')
        if {str(path): verify.sha(path) for path in toolchain} != toolchain_sha:
            raise RuntimeError('Toolchain executables changed during tutorial verification')
        current = verify.artifact_map(selected, locked, sysroot)
        current.update(tutorial_artifacts)
        if current != artifacts or verify.hash_artifacts(current, workers) != fingerprints:
            raise RuntimeError('Compiled artifacts changed during tutorial audit')
        report.update(status='passed', **audited,
                      artifact_inventory=verify.relative(out / 'artifact-sha256.json'))
        print(json.dumps(audited['summary'], indent=2), flush=True)
        return 0
    except (Exception, KeyboardInterrupt) as error:
        report.update(status='failed', error=str(error) or type(error).__name__)
        print('Example verification failed: ' + report['error'], file=sys.stderr, flush=True)
        return 1
    finally:
        report.update(finished_utc=verify.now(), elapsed_seconds=time.monotonic() - started)
        report['output_sha256'] = {verify.relative(path): verify.sha(path)
            for path in sorted(out.iterdir()) if path.is_file() and path != result}
        verify.save_json(result, report)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scope', choices=SCOPES, default='core')
    parser.add_argument('--workers', type=int, default=2)
    parser.add_argument('--no-build', action='store_true',
                        help='Reuse prerequisites already built by a matching verification profile')
    parser.add_argument('--project-root', type=Path, default=Path(__file__).resolve().parents[1],
                        help=argparse.SUPPRESS)
    args = parser.parse_args()
    if not 1 <= args.workers <= 32:
        parser.error('--workers must be between 1 and 32')
    root = args.project_root.resolve()
    verify = load_verifier(root)
    # Share the production driver's lock: prerequisite builds and artifact
    # hashing must not race another profile's Lake build in this checkout.
    lock = root / 'validation/.verify-lock'
    lock.parent.mkdir(parents=True, exist_ok=True)
    try:
        lock.mkdir()
    except FileExistsError:
        print(f'Another library/example verifier owns {lock}; inspect owner.json before removing a stale lock', file=sys.stderr)
        return 2
    try:
        import os
        verify.save_json(lock / 'owner.json', {'pid': os.getpid(), 'started_utc': verify.now(),
                                              'scope': 'examples-' + args.scope})
        return check(root, args.scope, args.workers, verify, build=not args.no_build)
    finally:
        shutil.rmtree(lock)


if __name__ == '__main__':
    raise SystemExit(main())
