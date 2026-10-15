#!/usr/bin/env python3
"""Verify the unified library: --scope core (default), algorithms, or all.

A source build plus Lean private-declaration/transitive-axiom audit, not independent
kernel replay. Lake's exact ownership is checked globally; Lean's own import parser
selects build inputs and its compiled environment independently checks the closure.
Only Python's standard library is required. All Lake calls use scripts/lake.

Results: validation/<scope>/result.json (schema 2). validation/result.json mirrors
only the latest core run. Historical outputs are archived before replacement.
--inventory-only records no successful proof audit. --self-test tests the harness.
"""
from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
if sys.version_info < (3, 11):
    raise SystemExit("Unified verification requires Python 3.11 or newer (standard-library tomllib).")
import tomllib

ROOT = Path(__file__).resolve().parents[1]
LAKE = ROOT / 'scripts/lake'
PACKAGES = {
    'countingComplexity': '.', 'countingHolantCore': 'projects/holant-core',
    'countingFoundations': 'projects/foundations',
    'partitionSemantics': 'projects/partition-semantics',
    'graphCSPReduction': 'projects/graph-csp-reduction',
    'countingInterpolation': 'projects/interpolation',
    'countingPfaffian': 'projects/pfaffian', 'countingKarpLuby': 'projects/karp-luby',
    'countingVariableElimination': 'projects/variable-elimination',
    'holantUnified': 'projects/holant-unified',
    'countingProductAlgorithm': 'projects/product-algorithm',
    'countingAffine': 'projects/affine-algorithm',
    'countingHolographic': 'projects/holographic',
    'countingMatchgateWidth': 'projects/matchgate-width',
    'countingComplexCSP': 'projects/complex-csp',
    'countingPlanarHom': 'projects/planar-homomorphisms',
    'countingPfaffianFinite': 'projects/pfaffian-finite',
    'countingWitnessMachines': 'projects/witness-machines',
    'countingVariableEliminationLayout': 'projects/variable-elimination-layout',
    'countingKarpLubyMachine': 'projects/karp-luby-machine',
    'countingVariableEliminationWork': 'projects/variable-elimination-work',
    'countingVariableEliminationWidth': 'projects/variable-elimination-width',
    'countingPlanarMachines': 'projects/planar-machines',
    'countingCookLevin': 'projects/counting-cook-levin',
    'countingInterpolationMachine': 'projects/interpolation-machine',
    'countingVariableEliminationTreewidth': 'projects/variable-elimination-treewidth',
    'countingKnowledgeCompilation': 'projects/knowledge-compilation',
    'countingChargedReductions': 'projects/charged-reductions',
    'countingPlanarAlgorithms': 'projects/planar-algorithms',
    'countingPlanarClassification': 'projects/planar-classification',
    'countingComplexCSPClassification': 'projects/complex-csp-classification',
    'countingKarpLubyRequest': 'projects/karp-luby-request',
    'countingOpenNetworkBridge': 'projects/open-network-bridge',
    'countingGadgetReductions': 'projects/gadget-reductions',
    'countingFieldArithmetic': 'projects/field-arithmetic',
    'countingSharpPClosure': 'projects/sharpp-closure',
    'countingProductMachineBridge': 'projects/product-machine-bridge',
    'countingTractableCore': 'projects/tractable-core',
}
REUSE = {'countingOpenNetworkBridge', 'countingGadgetReductions',
         'countingFieldArithmetic', 'countingSharpPClosure', 'countingProductMachineBridge'}
CORE = {'countingComplexity', 'countingHolantCore', 'countingFoundations',
        'partitionSemantics', 'graphCSPReduction', 'countingInterpolation',
        'countingPlanarHom', 'countingWitnessMachines', 'countingPlanarMachines',
        'countingCookLevin', 'countingChargedReductions'}
ALGORITHMS = {'countingPfaffian', 'countingKarpLuby', 'countingVariableElimination',
              'countingTractableCore',
              'countingProductAlgorithm', 'countingAffine', 'countingHolographic',
              'countingPfaffianFinite', 'countingVariableEliminationLayout',
              'countingKarpLubyMachine', 'countingVariableEliminationWork',
              'countingVariableEliminationWidth', 'countingInterpolationMachine',
              'countingVariableEliminationTreewidth', 'countingKnowledgeCompilation',
              'countingPlanarAlgorithms', 'countingKarpLubyRequest'}
FLAGSHIPS = {'holantUnified', 'countingMatchgateWidth', 'countingComplexCSP',
             'countingPlanarClassification', 'countingComplexCSPClassification'}
# H1 deliberately selects its reachable flagship closure from a larger snapshot.
# The other accepted flagship packages must be covered in their entirety.
COMPLETE_FLAGSHIPS = {'countingMatchgateWidth', 'countingComplexCSP',
                      'countingPlanarClassification', 'countingComplexCSPClassification'}
# Reject even generically named declarations owned by the complete classifiers.
CLASSIFICATION_ONLY = {'countingPlanarClassification', 'countingComplexCSPClassification'}
ALGORITHM_SUPPORT = {'holantUnified'}
# These explicitly optional upstream adapters have larger structural closures.
# The small Holographic API and its clients remain in algorithm acceptance.
ALL_ONLY_MODULES = {
    'Counting.Algorithm.Holographic.All',
    'Counting.Algorithm.Holographic.Upstream',
    'Counting.Algorithm.Holographic.FixedTables',
    'Counting.Algorithm.Holographic.PhysicalOpen',
}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
SKIP_DIRS = {'projects', 'notes', 'validation', 'Verification', 'audit', 'provenance', 'scripts'}
ACCEPTANCE = {'core': 'validation/All.lean', 'algorithms': 'validation/Algorithms.lean',
              'all': 'validation/Library.lean', 'reuse': 'validation/Reuse.lean'}
ROOT_LIBRARIES = {'core': {'Counting'}, 'algorithms': {'Counting', 'CountingAlgorithms'},
                  'all': {'Counting', 'CountingAlgorithms', 'CountingFlagships', 'CountingLibrary', 'CountingReuse'},
                  'reuse': {'CountingReuse'}}
AUDIT_SUFFIXES = ['-declarations.jsonl', '-external-declarations.jsonl', '-modules.jsonl',
                  '-codegen.jsonl', '-reexports.jsonl', '-axioms.jsonl', '-closure.jsonl', '-summary.json']


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open('rb') as handle:
        for chunk in iter(lambda: handle.read(2 ** 20), b''):
            digest.update(chunk)
    return digest.hexdigest()


def save_json(path: Path, data: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile('w', dir=path.parent, prefix=path.name + '.',
                                     suffix='.tmp', delete=False) as handle:
        json.dump(data, handle, ensure_ascii=False, indent=2)
        handle.write('\n')
        temporary = Path(handle.name)
    temporary.replace(path)


def records(path: Path):
    with path.open() as handle:
        for number, line in enumerate(handle, 1):
            if line.strip():
                try:
                    yield json.loads(line)
                except ValueError as error:
                    raise RuntimeError(f'Invalid JSONL {path}:{number}: {error}') from error


def relative(path: Path) -> str:
    return str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)


def selectors(lib: dict) -> set[tuple[str, str]]:
    """Lake LeanLibConfig.isLocalModule: root-prefix OR glob match."""
    roots = lib.get('roots', [lib['name']])
    result = {(root, 'tree') for root in roots}
    for glob in lib.get('globs', roots):
        if glob.endswith('.+'):
            result.add((glob[:-2], 'children'))
        elif glob.endswith('.*'):
            result.add((glob[:-2], 'tree'))
        else:
            result.add((glob, 'one'))
    return result


def selector_matches(module: str, selector: tuple[str, str]) -> bool:
    stem, kind = selector
    return ((module == stem and kind != 'children') or
            (module.startswith(stem + '.') and kind != 'one'))


def matches(module: str, lib: dict) -> bool:
    return any(selector_matches(module, selector) for selector in selectors(lib))


def overlap(left: tuple[str, str], right: tuple[str, str]) -> str | None:
    """Return a witness of intersecting Lake claims, even with no source files."""
    for witness in (left[0], right[0], left[0] + '.__ownership_probe',
                    right[0] + '.__ownership_probe'):
        if selector_matches(witness, left) and selector_matches(witness, right):
            return witness
    return None


def compile_library(lib: dict) -> tuple[frozenset, tuple]:
    specs = selectors(lib)
    return frozenset(stem for stem, kind in specs if kind == 'one'), tuple(spec for spec in specs if spec[1] != 'one')


def compiled_matches(module: str, rule: tuple) -> bool:
    exact, prefixes = rule
    return module in exact or any(selector_matches(module, prefix) for prefix in prefixes)


def validate_claims(claims: list[tuple[str, dict]]) -> None:
    compiled = [(owner, lib['name'], compile_library(lib)) for owner, lib in claims]
    for index, (owner, name, (exact, broad)) in enumerate(compiled):
        for other, other_name, (other_exact, other_broad) in compiled[index + 1:]:
            witness = next(iter(exact & other_exact), None)
            if witness is None:
                witness = next((m for m in exact if any(selector_matches(m, p) for p in other_broad)), None)
            if witness is None:
                witness = next((m for m in other_exact if any(selector_matches(m, p) for p in broad)), None)
            if witness is None:
                witness = next((w for p in broad for q in other_broad if (w := overlap(p, q))), None)
            if witness:
                raise RuntimeError(f'Duplicate Lake ownership: {owner}:{name} and '
                                   f'{other}:{other_name} both claim {witness}')


def configurations() -> dict[str, dict]:
    configs = {}
    for name, directory in PACKAGES.items():
        config = tomllib.loads((ROOT / directory / 'lakefile.toml').read_text())
        if config['name'] != name:
            raise RuntimeError(f'Unexpected package name in {directory}: {config["name"]}')
        if config.get('buildDir', '.lake/build') != '.lake/build' or config.get('leanLibDir', 'lib/lean') != 'lib/lean':
            raise RuntimeError(f'Unsupported compiled artifact directory in {name}; extend the verifier explicitly')
        if config.get('srcDir', '.') != '.':
            raise RuntimeError(f'Unsupported package srcDir in {name}; extend the verifier explicitly')
        for lib in config.get('lean_lib', []):
            if lib.get('srcDir', '.') != '.':
                raise RuntimeError(f'Unsupported library srcDir in {name}:{lib["name"]}')
        configs[name] = config
    declared = {entry['name']: entry.get('path') for entry in configs['countingComplexity'].get('require', [])}
    for name, directory in PACKAGES.items():
        if name != 'countingComplexity' and declared.get(name) != directory:
            raise RuntimeError(f'Root must require {name} at {directory}')
    return configs


def inventory(configs: dict) -> tuple[list[dict], list[dict]]:
    claims = [(name, lib) for name, config in configs.items() for lib in config.get('lean_lib', [])]
    validate_claims(claims)
    modules, excluded = {}, []
    ownership = {name: [(lib['name'], compile_library(lib)) for lib in config.get('lean_lib', [])]
                 for name, config in configs.items()}
    for name, directory in PACKAGES.items():
        package = ROOT / directory
        for current, dirs, files in os.walk(package):
            dirs[:] = sorted(d for d in dirs if not d.startswith('.') and d not in SKIP_DIRS)
            for filename in sorted(files):
                if not filename.endswith('.lean') or filename == 'lakefile.lean':
                    continue
                path = Path(current) / filename
                module = '.'.join(path.relative_to(package).with_suffix('').parts)
                owners = [name for name, rule in ownership[name] if compiled_matches(module, rule)]
                item = dict(module=module, path=relative(path), package=name, sha256=sha(path))
                if not owners:
                    excluded.append(dict(item, reason='outside Lake library ownership'))
                    continue
                if len(owners) != 1 or module in modules:
                    raise RuntimeError(f'Duplicate source provider for {module}: {path}')
                modules[module] = dict(item, library=owners[0])
    return sorted(modules.values(), key=lambda r: r['module']), sorted(excluded, key=lambda r: r['path'])


def dependencies(configs: dict) -> dict:
    baseline = None
    manifests = {}
    toolchains = set()
    for name, directory in PACKAGES.items():
        package = ROOT / directory
        manifest = json.loads((package / 'lake-manifest.json').read_text())
        if manifest.get('name') != name:
            raise RuntimeError(f'Manifest package name differs from configuration: {directory}')
        git = {p['name']: {'revision': p['rev'], 'url': p['url'], 'subdir': p.get('subDir')}
               for p in manifest['packages'] if p['type'] == 'git'}
        if len(git) != 9:
            raise RuntimeError(f'{name}: expected exactly nine locked Git dependencies, got {len(git)}')
        if baseline is None:
            baseline = git
        elif git != baseline:
            raise RuntimeError(f'Git dependency locks differ from root: {name}')
        local = {p['name']: p for p in manifest['packages'] if p['type'] == 'path'}
        for requirement in configs[name].get('require', []):
            if 'path' in requirement:
                entry = local.get(requirement['name'])
                expected = (package / requirement['path']).resolve()
                if entry is None or (package / entry['dir']).resolve() != expected:
                    raise RuntimeError(f'Stale local dependency manifest: {name} -> {requirement["name"]}')
            elif 'git' in requirement:
                pin = git.get(requirement['name'])
                if not pin or pin['url'] != requirement['git'] or pin['revision'] != requirement['rev']:
                    raise RuntimeError(f'Configured Git dependency differs from lock: {name}')
        if name == 'countingComplexity' and set(local) != set(PACKAGES) - {'countingComplexity'}:
            raise RuntimeError(f'Root manifest must contain exactly the {len(PACKAGES) - 1} local component packages')
        toolchains.add((package / 'lean-toolchain').read_text().strip())
        manifests[name] = sha(package / 'lake-manifest.json')
    if len(toolchains) != 1:
        raise RuntimeError(f'Mixed Lean toolchains: {sorted(toolchains)}')
    return {'toolchain': toolchains.pop(), 'git_dependencies': baseline, 'manifest_sha256': manifests}


def git_binary() -> str:
    fallback = Path.home() / '.cache/codex-runtimes/codex-primary-runtime/dependencies/bin/fallback/git'
    return str(fallback) if fallback.is_file() else 'git'


def installed_dependencies(locked: dict) -> dict:
    installed = {}
    for name, pin in locked['git_dependencies'].items():
        directory = ROOT / '.lake/packages' / name
        command = [git_binary(), '-C', str(directory)]
        actual = subprocess.check_output(command + ['rev-parse', 'HEAD'], text=True).strip()
        if actual != pin['revision']:
            raise RuntimeError(f'Installed dependency {name}: {actual} differs from lock {pin["revision"]}')
        dirty = subprocess.check_output(command + ['status', '--porcelain', '--untracked-files=all'], text=True)
        if dirty.strip():
            raise RuntimeError(f'Installed dependency {name} has tracked or nonignored untracked changes')
        installed[name] = {'head': actual, 'clean': True}
    return installed


def environment(workers: int) -> dict:
    env = dict(os.environ)
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    env.update(LEAN_NUM_THREADS=str(workers), MATHLIB_NO_CACHE_ON_UPDATE='1')
    return env


def terminate_process_group(process: subprocess.Popen, grace_seconds: float = 1.0) -> None:
    """Stop only the new session created for this command, including descendants.

    A group leader can exit on TERM while a child ignores it. Always send KILL to
    the original group afterwards, even when waiting for the leader succeeded.
    """
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        process.wait(timeout=grace_seconds)
    except subprocess.TimeoutExpired:
        pass
    finally:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    process.wait()


def run(args: list[str], log: Path, env: dict, commands: list, expected: int = 0) -> str:
    commands.append({'argv': [relative(Path(arg)) if arg.startswith('/') else arg for arg in args],
                     'log': relative(log), 'expected_exit_code': expected})
    print('Running: ' + ' '.join(args), flush=True)
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open('w') as output:
        process = subprocess.Popen(args, cwd=ROOT, env=env, stdout=output,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            process.wait()
        except BaseException:
            terminate_process_group(process)
            commands[-1].update(exit_code=process.returncode, interrupted=True)
            raise
        if process.returncode != expected:
            terminate_process_group(process)
    commands[-1]['exit_code'] = process.returncode
    text = log.read_text()
    if process.returncode != expected:
        print(text[-12000:], file=sys.stderr)
        raise RuntimeError(f'Command failed ({process.returncode}, expected {expected}); see {relative(log)}')
    return text


def import_graph(sources: list[dict], acceptance: str, out: Path, env: dict, commands: list) -> dict:
    request = out / 'import-request.json'
    entries = [(s['module'], s['path']) for s in sources] + [('@acceptance', acceptance)]
    save_json(request, entries)
    run([str(LAKE), 'env', 'lean', '--run', 'validation/ImportGraph.lean', str(request),
         str(out / 'import-graph.jsonl')], out / 'import-graph.log', env, commands)
    parsed = list(records(out / 'import-graph.jsonl'))
    graph = {r['module']: list(dict.fromkeys(r['imports'])) for r in parsed}
    if len(parsed) != len(entries) or set(graph) != {name for name, _ in entries}:
        raise RuntimeError('Lean import parser returned incomplete or duplicate module inventory')
    return graph


def module_closure(roots: list[str], graph: dict[str, list[str]]) -> set[str]:
    reached, pending = set(), list(roots)
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        reached.add(name)
        pending.extend(graph.get(name, []))
    return reached


def forbidden_light_module(name: str) -> bool:
    """Paper/flagship providers cannot silently enter the shared light layer."""
    return (name == 'Paper' or name.startswith(('Paper.', 'Paper2',
            'Counting.Paper', 'Counting.Classification', 'Counting.Flagships',
            'Counting.HolantUnified', 'Counting.MatchgateWidth', 'MatchgateWidth',
            'Counting.ComplexCSP', 'ComplexCSP')) or
            (name.startswith('Holant.') and ('.Classification' in name or
             name.startswith(('Holant.Proofs.Dichotomy', 'Holant.Dichotomy')))))


def light_closures(scope: str, graph: dict, sources: list[dict], compiled: bool = False) -> dict:
    by_name = {s['module']: s for s in sources}
    result = {}
    roots = ['Counting'] + (['Counting.Algorithms'] if scope != 'core' else [])
    if scope in {'reuse', 'all'} and 'Counting.Reuse' in graph:
        roots.append('Counting.Reuse')
    for root in roots:
        if root not in graph:
            raise RuntimeError(f'Missing light-layer root: {root}')
        reached = module_closure([root], graph)
        forbidden = sorted(name for name in reached if forbidden_light_module(name) or
                           by_name.get(name, {}).get('package') in CLASSIFICATION_ONLY)
        if forbidden:
            raise RuntimeError(f'Light entry {root} reaches paper/classification modules: {forbidden}')
        local = sorted(reached & by_name.keys())
        result[root] = {'local_modules': local,
                        'local_modules_by_package': dict(Counter(by_name[n]['package'] for n in local)),
                        'forbidden_modules': [], 'compiled_environment': compiled}
        if compiled:
            result[root]['all_import_modules'] = len(reached)
    return result


def select_scope(scope: str, sources: list[dict], graph: dict, configs: dict) -> list[dict]:
    by_name = {s['module']: s for s in sources}
    required = set()
    for source in sources:
        package = source['package']
        if package == 'countingComplexity':
            include = source['library'] in ROOT_LIBRARIES[scope]
        elif scope == 'reuse':
            include = package in REUSE
        else:
            include = (package in CORE or (scope != 'core' and package in ALGORITHMS) or
                       (scope == 'all' and package in (COMPLETE_FLAGSHIPS | REUSE)))
        if include and (scope == 'all' or source['module'] not in ALL_ONLY_MODULES):
            required.add(source['module'])
    claims = [compile_library(lib) for config in configs.values() for lib in config.get('lean_lib', [])]
    pending = list(graph['@acceptance'])
    reached = set()
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        if name not in by_name:
            # A claimed import without a source must not quietly resolve from a cache.
            if any(compiled_matches(name, rule) for rule in claims):
                raise RuntimeError(f'Imported local module has no owned source: {name}')
            continue
        reached.add(name)
        pending.extend(graph[name])
    missing = required - reached
    if missing:
        raise RuntimeError(f'Acceptance omits owned {scope} production modules: {sorted(missing)}')
    unexpected = {name for name in reached if name not in required and
                  scope != 'reuse' and
                  not (scope == 'all' and by_name[name]['package'] in FLAGSHIPS) and
                  not (scope == 'algorithms' and by_name[name]['package'] in ALGORITHM_SUPPORT)}
    if unexpected:
        raise RuntimeError(f'{scope} imports modules outside its declared profile: {sorted(unexpected)}')
    if not reached:
        raise RuntimeError('Empty production import closure')
    if scope != 'all':
        forbidden = sorted(name for name in reached if forbidden_light_module(name))
        if forbidden:
            raise RuntimeError(f'{scope} acceptance reaches paper/classification modules: {forbidden}')
    return [by_name[name] for name in sorted(reached)]


def harness_snapshot(configs: dict) -> dict:
    paths = [ROOT / 'scripts/verify.py', ROOT / 'tests/test_verify_receipts.py', LAKE, *sorted((ROOT / 'validation').glob('*.lean'))]
    for name, directory in PACKAGES.items():
        paths.extend(ROOT / directory / f for f in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain'])
    return {relative(path): sha(path) for path in paths}


def artifact_entry(path: Path) -> list[list[str]]:
    # Positional ImportArtifacts representation: olean, server, private; then IR.
    parts = [path]
    for suffix in ['.server', '.private']:
        extra = Path(str(path) + suffix)
        if extra.exists():
            if suffix == '.private' and len(parts) != 2:
                raise RuntimeError(f'Private artifact without server artifact: {extra}')
            parts.append(extra)
    ir = path.with_suffix('.ir')
    ir_sig = path.with_suffix('.ir.sig')
    code = [ir_sig, ir] if ir_sig.exists() and ir.exists() else ([ir_sig] if ir_sig.exists() else ([ir] if ir.exists() else []))
    return [[str(p) for p in parts], [str(p) for p in code]]


def artifact_map(sources: list[dict], locked: dict, sysroot: Path) -> dict:
    artifacts = {}
    for source in sources:
        package = ROOT / PACKAGES[source['package']]
        path = package / '.lake/build/lib/lean' / Path(*source['module'].split('.')).with_suffix('.olean')
        if not path.is_file():
            raise RuntimeError(f'Missing source build artifact: {relative(path)}')
        artifacts[source['module']] = artifact_entry(path)
    roots = [ROOT / '.lake/packages' / name / '.lake/build/lib/lean' for name in locked['git_dependencies']]
    roots.append(sysroot / 'lib/lean')
    for root in roots:
        for path in sorted(root.rglob('*.olean')):
            name = '.'.join(path.relative_to(root).with_suffix('').parts)
            if name in artifacts:
                raise RuntimeError(f'Conflicting local/external compiled module provider: {name}')
            artifacts[name] = artifact_entry(path)
    return artifacts


def hash_artifacts(artifacts: dict, workers: int) -> dict:
    paths = sorted({path for parts in artifacts.values() for group in parts for path in group})
    def fingerprint(filename):
        path = Path(filename)
        before = path.stat()
        digest = sha(path)
        after = path.stat()
        if (before.st_size, before.st_mtime_ns) != (after.st_size, after.st_mtime_ns):
            raise RuntimeError(f'Artifact changed while hashing: {filename}')
        return relative(path), {'sha256': digest, 'bytes': after.st_size}
    with ThreadPoolExecutor(max_workers=workers) as pool:
        return dict(pool.map(fingerprint, paths))


def validate_audit(prefix: Path, selected: list[dict], artifacts: dict) -> dict:
    suffix = lambda value: Path(str(prefix) + value)
    summary = json.loads(suffix('-summary.json').read_text())
    if summary.get('status') != 'passed':
        raise RuntimeError('Lean audit did not emit a passing summary')
    module_set = {s['module'] for s in selected}
    modules = list(records(suffix('-modules.jsonl')))
    if len(modules) != len(module_set) or {r['name'] for r in modules} != module_set:
        raise RuntimeError('Compiled module coverage differs from exact source inventory')
    closure = list(records(suffix('-closure.jsonl')))
    if len({r['name'] for r in closure}) != len(closure):
        raise RuntimeError('Duplicate actual import closure entries')
    if {r['name'] for r in closure if r['production_owned']} != module_set:
        raise RuntimeError('Actual compiled import closure differs from selected modules')
    missing_artifacts = {r['name'] for r in closure} - set(artifacts)
    if missing_artifacts:
        raise RuntimeError(f'Imported modules lack artifact fingerprints: {sorted(missing_artifacts)}')
    names, kinds, observed, counts = set(), Counter(), set(), Counter()
    for record in records(suffix('-declarations.jsonl')):
        name = record['name']
        if name in names or record['module'] not in module_set:
            raise RuntimeError(f'Duplicate or incorrectly owned declaration: {name}')
        names.add(name)
        if record['kind'] == 'axiom' or set(record['axioms']) - ALLOWED_AXIOMS:
            raise RuntimeError(f'Disallowed local declaration/axiom: {name}')
        if record.get('type_representation') != 'Lean.Expr structural hash' or not record.get('type_hash'):
            raise RuntimeError(f'Missing structural type fingerprint: {name}')
        kinds[record['kind']] += 1
        counts[record['module']] += 1
        observed.update(record['axioms'])
    if not names or not kinds['theorem'] or len(names) != summary['declarations']:
        raise RuntimeError('Declaration count is empty or inconsistent')
    external, export_counts = set(), Counter()
    for record in records(suffix('-external-declarations.jsonl')):
        name = record['name']
        if name in names or name in external or record['module'] in module_set or not record['production_exporters']:
            raise RuntimeError(f'Invalid canonical owner or duplicate external exported declaration: {name}')
        external.add(name)
        if set(record['axioms']) - ALLOWED_AXIOMS:
            raise RuntimeError(f'Disallowed external export dependency: {name}')
        if record.get('type_representation') != 'Lean.Expr structural hash' or not record.get('type_hash'):
            raise RuntimeError(f'Missing external structural type fingerprint: {name}')
        observed.update(record['axioms'])
        for exporter in record['production_exporters']:
            if exporter['module'] not in module_set or exporter['pool'] not in {'constNames', 'extraConstNames'}:
                raise RuntimeError(f'Invalid production exporter: {name}')
            export_counts[exporter['module']] += 1
    if len(external) != summary['external_export_declarations'] or len(names) + len(external) != summary['audited_kernel_roots']:
        raise RuntimeError('External-export root counts differ from Lean summary')
    for record in modules:
        name = record['name']
        if counts[name] != record['kernel_declarations']:
            raise RuntimeError(f'Module declaration count mismatch: {name}')
        if record['exported_kernel_entries'] + record['compiler_only_entries'] != record['module_constant_names'] + record['module_extra_names']:
            raise RuntimeError(f'Module export inventory incompletely reconciled: {name}')
        if export_counts[name] != record['exported_external_kernel_entries']:
            raise RuntimeError(f'External export ledger mismatch: {name}')
    reexports = list(records(suffix('-reexports.jsonl')))
    if len(reexports) != summary['compatible_repeated_source_exports']:
        raise RuntimeError('Repeated-export count differs from Lean summary')
    for record in reexports:
        if record['name'] not in names | external or record['exporting_module'] not in module_set:
            raise RuntimeError(f'Reexport omitted from independent audit: {record["name"]}')
    codegen = list(records(suffix('-codegen.jsonl')))
    if len(codegen) != summary['compiler_auxiliaries_without_kernel_declarations']:
        raise RuntimeError('Compiler-only auxiliary count differs from Lean summary')
    if any(r['module'] not in module_set for r in codegen):
        raise RuntimeError('Compiler-only record has an unexpected module owner')
    axiom_records = list(records(suffix('-axioms.jsonl')))
    if any(not r['permitted'] or r['name'] not in ALLOWED_AXIOMS for r in axiom_records):
        raise RuntimeError('Disallowed reachable graph axiom')
    if any(summary[key] != 0 for key in ['local_axioms', 'disallowed_dependencies', 'external_export_disallowed_dependencies']):
        raise RuntimeError('Nonzero forbidden-axiom count in passing summary')
    if summary['modules'] != len(module_set) or summary['theorems'] != kinds['theorem'] or set(summary['observed_axioms']) != observed:
        raise RuntimeError('Audit summary does not reconcile with declaration records')
    return {'summary': summary, 'declaration_kinds': dict(sorted(kinds.items())),
            'observed_axioms': sorted(observed), 'actual_import_modules': len(closure)}


def archive_existing(out: Path) -> str | None:
    if not out.exists() or not any(out.iterdir()):
        return None
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    target = ROOT / 'validation/history' / (out.name + '-' + stamp)
    shutil.copytree(out, target)
    # Copy is deliberate: previous evidence survives even if the next run fails.
    return relative(target)


def last_passed_baseline(scope: str, immediate: str | None) -> str | None:
    """Comparison deltas use the latest passing receipt, never a failed retry."""
    candidates = ([ROOT / immediate] if immediate else []) + sorted(
        (ROOT / 'validation/history').glob(scope + '-*'), reverse=True)
    for directory in dict.fromkeys(candidates):
        receipt = directory / 'result.json'
        if receipt.is_file() and json.loads(receipt.read_text()).get('status') == 'passed':
            if (directory / 'sources.json').is_file() and (directory / 'audit-closure.jsonl').is_file():
                return relative(directory)
    return None


def verify(args) -> int:
    out = ROOT / 'validation' / ('inventory' if args.inventory_only else '') / args.scope
    archive = archive_existing(out)
    baseline = last_passed_baseline(args.scope, archive)
    if out.exists():
        shutil.rmtree(out)
    out.mkdir(parents=True, exist_ok=True)
    result_path = out / 'result.json'
    report = {'schema_version': 2, 'status': 'running', 'profile': args.scope, 'started_utc': now(),
              'scope': 'Source build and Lean declaration/transitive-axiom audit; not independent kernel replay',
              'type_recording': 'Every audited kernel type has a Lean.Expr structural hash and direct constant dependencies; these are not full rendered types or cryptographic proof certificates',
              'workers': args.workers, 'worker_control': 'LEAN_NUM_THREADS bounds each Lean/Lake runtime task pool; package compiler options may restrict it further',
              'previous_evidence': archive, 'commands': [], 'inventory_only': args.inventory_only}
    if baseline:
        report['comparison_baseline'] = {'path': baseline, 'status': 'passed',
            'receipt_sha256': sha(ROOT / baseline / 'result.json'),
            'selection': 'latest passing profile receipt with source and compiled closure inventories'}
    def persist():
        save_json(result_path, report)
        if args.scope == 'core' and not args.inventory_only:
            save_json(ROOT / 'validation/result.json', dict(report, compatibility_alias='latest core profile only',
                      canonical_result='validation/core/result.json'))
    persist()
    started = time.monotonic()
    try:
        configs = configurations()
        sources, excluded = inventory(configs)
        locked = dependencies(configs)
        watched = harness_snapshot(configs)
        env = environment(args.workers)
        report.update(dependencies=locked, input_sha256=watched)
        report['installed_dependencies'] = installed_dependencies(locked)
        version = run([str(LAKE), 'env', 'lean', '--version'], out / 'lean-version.log', env, report['commands']).strip()
        report['lean_version'] = version
        expected_version = locked['toolchain'].split(':v')[-1]
        if f'version {expected_version}' not in version:
            raise RuntimeError('Installed Lean version differs from toolchain lock')
        sysroot = Path(run([str(LAKE), 'env', 'lean', '--print-prefix'], out / 'lean-prefix.log', env, report['commands']).strip())
        toolchain_files = [sysroot / 'bin' / name for name in ['lean', 'lake', 'leanc'] if (sysroot / 'bin' / name).is_file()]
        toolchain_hashes = {str(path): sha(path) for path in toolchain_files}
        report['toolchain_binary_sha256'] = toolchain_hashes
        graph = import_graph(sources, ACCEPTANCE[args.scope], out, env, report['commands'])
        selected = select_scope(args.scope, sources, graph, configs)
        report['light_entry_source_closures'] = light_closures(args.scope, graph, sources)
        save_json(out / 'sources.json', selected)
        save_json(out / 'ownership-inventory.json', sources)
        selected_names = {s['module'] for s in selected}
        report['optional_upstream_adapters'] = {
            'description': 'Explicit upstream adapters, outside the minimal mathematical algorithm kernel; all profile covers all four',
            'selected': sorted(selected_names & ALL_ONLY_MODULES),
            'deferred_to_all': sorted(ALL_ONLY_MODULES - selected_names)}
        roots = [name for name in graph['@acceptance'] if name in selected_names]
        excluded += [dict(s, reason='owned source outside this acceptance import closure') for s in sources if s['module'] not in selected_names]
        save_json(out / 'excluded-sources.json', excluded)
        report.update(source_modules=len(selected), source_modules_by_package=dict(Counter(s['package'] for s in selected)),
                      source_inventory=relative(out / 'sources.json'), excluded_source_inventory=relative(out / 'excluded-sources.json'),
                      acceptance_roots=roots)
        if baseline:
            previous = {s['module']: s for s in json.loads((ROOT / baseline / 'sources.json').read_text())}
            current = {s['module']: s for s in selected}
            report['source_delta'] = {
                'added': sorted(current.keys() - previous.keys()),
                'removed': sorted(previous.keys() - current.keys()),
                'changed': sorted(n for n in current.keys() & previous.keys()
                                  if current[n]['sha256'] != previous[n]['sha256'])}
        print(f'{args.scope}: {len(selected)} source modules selected; global provider claims and nine Git locks match', flush=True)
        persist()
        if args.inventory_only:
            if configurations() != configs or inventory(configs)[0] != sources or harness_snapshot(configs) != watched:
                raise RuntimeError('Source/configuration/harness changed during inventory')
            report['output_sha256'] = {relative(p): sha(p) for p in out.iterdir() if p.is_file() and p != result_path}
            report['status'] = 'inventoried'
            report['scope'] = 'Ownership, Lean source-header closure, dependencies only; no build or declaration audit'
            return 0
        targets = ['+' + name for name in roots]
        run([str(LAKE), '--no-cache', '--no-ansi', 'build', *targets], out / 'build.log', env, report['commands'])
        run([str(LAKE), '--no-cache', '--no-ansi', 'lean', ACCEPTANCE[args.scope]], out / 'imports.log', env, report['commands'])
        if inventory(configs)[0] != sources or harness_snapshot(configs) != watched:
            raise RuntimeError('Source/configuration/harness changed during build; rerun on a stable tree')
        artifacts = artifact_map(selected, locked, sysroot)
        print(f'Fingerprinting compiled inputs for {len(artifacts)} available local/dependency/toolchain modules', flush=True)
        fingerprints = hash_artifacts(artifacts, args.workers)
        save_json(out / 'artifact-sha256.json', fingerprints)
        save_json(out / 'audit-request.json', {'modules': [s['module'] for s in selected],
                  'all_local_modules': [s['module'] for s in sources], 'roots': roots,
                  'import_artifacts': artifacts})
        request_digest = sha(out / 'audit-request.json')
        prefix = out / 'audit'
        audit_output = run([str(LAKE), 'env', 'lean', '-M24000', '--run', 'validation/Audit.lean',
                           str(out / 'audit-request.json'), str(prefix)], out / 'audit.log', env, report['commands'])
        if sum(line.startswith('AUDIT_SUMMARY ') for line in audit_output.splitlines()) != 1:
            raise RuntimeError('Missing unique Lean audit completion marker')
        audited = validate_audit(prefix, selected, artifacts)
        compiled_graph = {r['name']: r['imports'] for r in records(out / 'audit-closure.jsonl')}
        for source in selected:
            name = source['module']
            if set(compiled_graph[name]) != set(graph[name]):
                raise RuntimeError(f'Compiled imports differ from parsed source header: {name}')
        report['light_entry_compiled_closures'] = light_closures(args.scope, compiled_graph, sources, compiled=True)
        for name, item in report['light_entry_source_closures'].items():
            if item['local_modules'] != report['light_entry_compiled_closures'][name]['local_modules']:
                raise RuntimeError(f'Source and compiled light closures disagree for {name}')
        if args.scope != 'all':
            forbidden = sorted(n for n in compiled_graph if forbidden_light_module(n))
            if forbidden:
                raise RuntimeError(f'Compiled {args.scope} closure contains forbidden imports: {forbidden}')
        if baseline:
            previous = {r['name'] for r in records(ROOT / baseline / 'audit-closure.jsonl')}
            report['compiled_closure_delta'] = {
                'added': sorted(compiled_graph.keys() - previous),
                'removed': sorted(previous - compiled_graph.keys())}
        print(f'Rechecking source, configuration, dependency, harness, and compiled input stability', flush=True)
        if configurations() != configs or inventory(configs)[0] != sources or dependencies(configs) != locked:
            raise RuntimeError('Sources or package configuration changed during verification')
        if harness_snapshot(configs) != watched or sha(out / 'audit-request.json') != request_digest:
            raise RuntimeError('Verification harness or audit request changed during verification')
        if installed_dependencies(locked) != report['installed_dependencies']:
            raise RuntimeError('Installed dependency state changed during verification')
        if {str(path): sha(path) for path in toolchain_files} != toolchain_hashes:
            raise RuntimeError('Toolchain executables changed during verification')
        if artifact_map(selected, locked, sysroot) != artifacts or hash_artifacts(artifacts, args.workers) != fingerprints:
            raise RuntimeError('Compiled artifacts changed during audit')
        report.update(status='passed', **audited, project_artifacts_copied_by_verifier=False,
                      cache_history='Preparation before this invocation is not inferred; record any cache bootstrap separately.',
                      build_mode='Lake source build with locked external caches and valid incremental artifacts; no cold-build claim',
                      artifact_inventory=relative(out / 'artifact-sha256.json'))
        outputs = [p for p in out.iterdir() if p.is_file() and p != result_path and not p.name.endswith('.tmp')]
        report['output_sha256'] = {relative(p): sha(p) for p in sorted(outputs)}
        print(json.dumps(audited['summary'], ensure_ascii=False), flush=True)
        return 0
    except (Exception, KeyboardInterrupt) as error:
        report.update(status='failed', error=str(error) or type(error).__name__)
        print('Verification failed: ' + report['error'], file=sys.stderr, flush=True)
        return 1
    finally:
        report.update(finished_utc=now(), elapsed_seconds=time.monotonic() - started)
        persist()


def self_test_checks() -> None:
    # Pure Python negative checks do not mutate production configuration or proofs.
    assert CORE.isdisjoint(ALGORITHMS)
    assert REUSE.isdisjoint(CORE | ALGORITHMS | FLAGSHIPS)
    assert CORE | ALGORITHMS | FLAGSHIPS | REUSE == set(PACKAGES)
    assert 'countingVariableElimination' in ALGORITHMS
    assert 'countingProductAlgorithm' in ALGORITHMS
    assert module_closure(['A'], {'A': ['B'], 'B': ['A', 'C']}) == {'A', 'B', 'C'}
    assert forbidden_light_module('Paper2.Classifier')
    assert forbidden_light_module('Holant.Proofs.Dichotomy.Main')
    assert forbidden_light_module('Counting.ComplexCSP.Recognition')
    assert not forbidden_light_module('Counting.Bridge.ComplexCSP')
    assert not forbidden_light_module('Holant.Proofs.Tractability.ProductElimination')
    try:
        light_closures('core', {'Counting': ['Paper2.Classifier']}, [])
    except RuntimeError:
        pass
    else:
        raise RuntimeError('Paper import in light entry was accepted')
    assert matches('Counting.A.B', {'name': 'Counting'})
    assert not matches('Counting', {'name': 'X', 'roots': [], 'globs': ['Counting.+']})
    assert matches('Counting.A', {'name': 'X', 'roots': [], 'globs': ['Counting.*']})
    assert not matches('Counting.Other', {'name': 'X', 'roots': [], 'globs': ['Counting.A']})
    assert overlap(('Counting', 'children'), ('Counting.A', 'children'))
    assert not overlap(('Counting.A', 'one'), ('Counting.A', 'children'))
    # The optimized H1-scale matcher must preserve every exact/root/glob rule.
    fixtures = [{'name': 'Counting'}, {'name': 'Counting.A'},
                {'name': 'X', 'roots': []},
                *({'name': 'X', 'roots': [], 'globs': [glob]} for glob in
                  ['Counting', 'Counting.+', 'Counting.*', 'Counting.A', 'Counting.A.+'])]
    for left in fixtures:
        for right in fixtures:
            intersects = any(overlap(p, q) for p in selectors(left) for q in selectors(right))
            try:
                validate_claims([('left', left), ('right', right)])
                optimized_intersects = False
            except RuntimeError:
                optimized_intersects = True
            assert optimized_intersects == intersects
        for module in ['Counting', 'Counting.A', 'Counting.A.B', 'Counting.B', 'Other']:
            assert compiled_matches(module, compile_library(left)) == matches(module, left)
    validate_claims([('a', {'name': 'A', 'roots': [], 'globs': ['Counting.A']}),
                     ('b', {'name': 'B', 'roots': [], 'globs': ['Counting.B']})])
    try:
        validate_claims([('a', {'name': 'Counting'}),
                         ('b', {'name': 'B', 'roots': [], 'globs': ['Counting.NothingHere.+']})])
    except RuntimeError:
        pass
    else:
        raise RuntimeError('Empty overbroad provider-claim fixture was accepted')
    fixture_configs = {'p': {'lean_lib': [{'name': 'X', 'roots': [], 'globs': ['Missing.Module']}]}}
    try:
        select_scope('core', [], {'@acceptance': ['Missing.Module']}, fixture_configs)
    except RuntimeError:
        pass
    else:
        raise RuntimeError('A claimed import without a source was accepted')
    # An accepted finite flagship package cannot hide unimported owned modules.
    try:
        select_scope('all', [{'module': 'Counting.ComplexCSP.Omitted',
                             'package': 'countingComplexCSP'}],
                     {'@acceptance': []}, {})
    except RuntimeError as error:
        assert 'Acceptance omits owned all production modules' in str(error)
    else:
        raise RuntimeError('An owned flagship module missing from acceptance was accepted')


def self_test(args) -> int:
    out = ROOT / 'validation/selftest'
    archive = archive_existing(out)
    out.mkdir(parents=True, exist_ok=True)
    report = {'schema_version': 2, 'status': 'running', 'started_utc': now(),
              'scope': 'verification harness only; no production verification',
              'previous_evidence': archive, 'commands': []}
    save_json(out / 'result.json', report)
    try:
        self_test_checks()
        env = environment(args.workers)
        run([str(LAKE), 'env', 'lean', '--run', 'validation/Audit.lean', '--self-test'],
            out / 'algorithm.log', env, report['commands'])
        modules = ['AuditFixture', 'AuditRejectFixture', 'AuditExportBase', 'AuditExportFirst',
                   'AuditExportGenerated', 'AuditExportFixture']
        arts = {}
        for module in modules:
            name = 'validation.' + module
            setup = out / 'setup.json'
            save_json(setup, {'name': name, 'package?': None, 'isModule': False, 'imports?': None, 'importArts': arts, 'dynlibs': [], 'plugins': [], 'options': {}})
            olean = out / (module + '.olean')
            run([str(LAKE), 'env', 'lean', '--setup', str(setup), '-o', str(olean),
                 f'validation/{module}.lean'], out / (module + '.log'), env, report['commands'])
            arts[name] = artifact_entry(olean)
        def audit_case(label, roots, selected, all_names, expected=0):
            request = out / (label + '-request.json')
            save_json(request, {'roots': roots, 'modules': selected, 'all_local_modules': all_names,
                                'import_artifacts': arts})
            return run([str(LAKE), 'env', 'lean', '--run', 'validation/Audit.lean', str(request), str(out / label)],
                       out / (label + '.log'), env, report['commands'], expected)
        fixture = 'validation.AuditFixture'
        audit_case('positive', [fixture], [fixture], [fixture])
        declarations = list(records(out / 'positive-declarations.jsonl'))
        by_name = {r['name']: r for r in declarations}
        assert any(r['private'] and 'privatePropext' in r['name'] for r in declarations)
        assert by_name['CountingAuditFixture.viaPrivate']['axioms'] == ['propext']
        assert by_name['CountingAuditFixture.choose']['axioms'] == ['Classical.choice']
        assert by_name['CountingAuditFixture.alternate_zero']['axioms'] == []
        assert any(r['kind'] == 'constructor' for r in declarations)
        assert any(r['kind'] == 'recursor' for r in declarations)
        missing = audit_case('missing', [fixture], [fixture, 'validation.Absent'], [fixture, 'validation.Absent'], 1)
        assert 'Expected source module absent' in missing
        omission = audit_case('omitted', [fixture], ['validation.Absent'], [fixture, 'validation.Absent'], 1)
        assert 'Expected source module absent' in omission
        rejected = 'validation.AuditRejectFixture'
        audit_case('rejected', [rejected], [rejected], [rejected], 1)
        summary = json.loads((out / 'rejected-summary.json').read_text())
        assert summary['local_axioms'] == 0 and summary['disallowed_dependencies'] > 0
        assert 'Lean.ofReduceBool' in summary['observed_axioms']
        exports = ['validation.AuditExportFixture', 'validation.AuditExportGenerated']
        omitted_export = audit_case('omitted-export', [exports[0]], [exports[0]], exports, 1)
        assert 'Source module omitted' in omitted_export
        audit_case('exports', [exports[0]], exports, exports)
        external = list(records(out / 'exports-external-declarations.jsonl'))
        assert any(r['name'] == 'CountingAuditExport.branching.eq_1' for r in external)
        assert all(r['production_exporters'] for r in external)
        # Test the Python ledger validator against real Lean output, including mutation rejection.
        fake_sources = [{'module': fixture}]
        closure_names = [r['name'] for r in records(out / 'positive-closure.jsonl')]
        validate_audit(out / 'positive', fake_sources, dict.fromkeys(closure_names))
        old = (out / 'positive-summary.json').read_text()
        bad = json.loads(old)
        bad['declarations'] += 1
        save_json(out / 'positive-summary.json', bad)
        try:
            validate_audit(out / 'positive', fake_sources, dict.fromkeys(closure_names))
        except RuntimeError:
            pass
        else:
            raise RuntimeError('Mutated declaration count was accepted')
        (out / 'positive-summary.json').write_text(old)
        report.update(status='passed', checks=['exact Lake ownership semantics', 'empty broadened claims rejected',
          'claimed import without source rejected', 'cycle fixed point', 'distinct independent axioms',
          'private declarations and proof dependencies', 'generated constructors and recursors',
          'missing import rejected', 'forbidden external compiler-trust axiom rejected',
          'external canonical generated reexport independently audited', 'tampered audit ledger rejected',
          'cyclic module import closure', 'paper/classification import in light entry rejected',
          'missing owned module in a complete flagship rejected'],
          fixture_declarations=len(declarations))
        print(json.dumps({key: value for key, value in report.items() if key != 'commands'}, ensure_ascii=False, indent=2))
        return 0
    except (Exception, KeyboardInterrupt) as error:
        report.update(status='failed', error=str(error) or type(error).__name__)
        print('Self-test failed: ' + report['error'], file=sys.stderr)
        return 1
    finally:
        report['finished_utc'] = now()
        save_json(out / 'result.json', report)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scope', choices=ACCEPTANCE, default='core')
    parser.add_argument('--workers', type=int, default=2,
                        help='Lean/Lake runtime workers and Python hash workers (1–32; default 2)')
    parser.add_argument('--inventory-only', action='store_true')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if not 1 <= args.workers <= 32:
        parser.error('--workers must be between 1 and 32')
    if args.inventory_only and args.self_test:
        parser.error('--inventory-only and --self-test are mutually exclusive')
    # mkdir is portable and atomic: one verifier owns root build/audit outputs.
    lock = ROOT / 'validation/.verify-lock'
    try:
        lock.mkdir()
    except FileExistsError:
        print(f'Another verifier owns {lock}; after an interrupted process, inspect owner.json before removing the lock', file=sys.stderr)
        return 1
    try:
        save_json(lock / 'owner.json', {'pid': os.getpid(), 'started_utc': now(), 'scope': args.scope})
        return self_test(args) if args.self_test else verify(args)
    finally:
        shutil.rmtree(lock)


if __name__ == '__main__':
    raise SystemExit(main())
