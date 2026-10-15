#!/usr/bin/env python3
"""Run serial release checks and bind their receipts to one committed source tree.

The optional --source-only preflight cannot produce release-ready status. A complete
run also installs the exact commit through its public Git URL in a fresh consumer.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

from check_downstream import environment, now, run, save, SHA

ROOT = Path(__file__).resolve().parents[1]
PROFILES = ('core', 'algorithms', 'reuse', 'all')
# These are regenerated verification outputs, not proof/configuration inputs.
OUTPUT_PREFIXES = tuple(f'validation/{p}/' for p in (*PROFILES, 'selftest', 'history', 'examples'))
OUTPUT_FILES = {'validation/result.json'}


def generated(path):
    return path in OUTPUT_FILES or path.startswith(OUTPUT_PREFIXES)


def git(source, env, *args):
    return subprocess.check_output(['git', '-C', str(source), *args], env=env)


def tracked_snapshot(source, env):
    paths = git(source, env, 'ls-files', '-z').decode().split('\0')
    hashes = {}
    for relative in filter(None, paths):
        if generated(relative):
            continue
        path = source / relative
        content = os.readlink(path).encode() if path.is_symlink() else path.read_bytes()
        hashes[relative] = hashlib.sha256(content).hexdigest()
    return hashes


def resources(source):
    try:
        memory = os.sysconf('SC_PAGE_SIZE') * os.sysconf('SC_PHYS_PAGES')
    except (ValueError, OSError):
        memory = 0
    return {'memory_bytes': memory, 'free_disk_bytes': shutil.disk_usage(source).free,
            'logical_cpus': os.cpu_count()}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path, required=True, help='New evidence directory; never overwritten')
    parser.add_argument('--commit', required=True, help='Exact committed source SHA')
    parser.add_argument('--repository', default='https://github.com/liuchliuch/countinglib')
    parser.add_argument('--workers', type=int, default=2)
    parser.add_argument('--source-only', action='store_true', help='Preflight before pushing; does not authorize tagging a release')
    args = parser.parse_args(argv)
    if not SHA.fullmatch(args.commit) or not 1 <= args.workers <= 32:
        parser.error('Use a full lowercase commit SHA and 1–32 workers')
    source, output = args.source.resolve(), args.output.absolute()
    receipt = None
    env = environment()
    env['LEAN_NUM_THREADS'] = str(args.workers)
    try:
        if git(source, env, 'rev-parse', 'HEAD').decode().strip() != args.commit:
            raise ValueError('Checkout HEAD does not match --commit')
        dirty = git(source, env, 'diff', '--name-only', 'HEAD', '-z').decode().split('\0')
        if any(not generated(path) for path in filter(None, dirty)):
            raise ValueError('Commit all changed release inputs before running the gate')
        untracked = git(source, env, 'ls-files', '--others', '--exclude-standard', '-z').decode().split('\0')
        if any(not generated(path) for path in filter(None, untracked)):
            raise ValueError('Untracked release inputs are present; commit them or use an isolated checkout')
        initial = tracked_snapshot(source, env)
        capacity = resources(source)
        if capacity['memory_bytes'] < 64 * 1024**3 or capacity['free_disk_bytes'] < 32 * 1024**3:
            raise ValueError('Full gate requires at least 64 GiB physical memory and 32 GiB free disk; the established local host has 128 GiB')
        output.mkdir(parents=True, exist_ok=False)
        receipt = {'schema_version': 1, 'status': 'running', 'started_utc': now(),
                   'commit': args.commit, 'resources': capacity, 'commands': [],
                   'profile_results': {}, 'tracked_input_sha256': initial,
                   'scope': 'Serial builds, private/generated declaration and axiom audits, seven fresh tutorial clients, exact Git-SHA installation; no independent kernel replay claim'}
        save(output / 'result.json', receipt)
        commands = [
            [sys.executable, 'scripts/check_public_docs.py'],
            [sys.executable, 'scripts/build_api_site.py', '--check'],
            [sys.executable, '-m', 'unittest', 'discover', '-s', 'tests', '-v'],
            ['./scripts/lake', 'exe', 'cache', 'get'],
            [sys.executable, 'scripts/verify.py', '--self-test', '--workers', str(args.workers)],
        ]
        for index, command in enumerate(commands):
            run(command, source, output / f'preflight-{index}.log', env, receipt)
        harness = source / 'validation/selftest/result.json'
        shutil.copyfile(harness, output / 'selftest-result.json')
        receipt['harness_result_sha256'] = hashlib.sha256(harness.read_bytes()).hexdigest()
        for profile in PROFILES:
            run([sys.executable, 'scripts/verify.py', '--scope', profile, '--workers', str(args.workers)],
                source, output / f'{profile}.log', env, receipt)
            result = source / f'validation/{profile}/result.json'
            data = json.loads(result.read_text())
            if data.get('status') != 'passed':
                raise ValueError(f'{profile} did not produce a passing proof receipt')
            archived = output / f'{profile}-result.json'
            shutil.copyfile(result, archived)
            receipt['profile_results'][profile] = {
                'receipt': archived.name, 'sha256': hashlib.sha256(archived.read_bytes()).hexdigest(),
                'source_modules': data.get('source_modules'), 'summary': data.get('summary')}
        run([sys.executable, 'scripts/check_examples.py', '--scope', 'all', '--workers', str(args.workers)],
            source, output / 'examples.log', env, receipt)
        if not args.source_only:
            run([sys.executable, 'scripts/check_downstream.py', '--source', str(source),
                 '--repository', args.repository, '--revision', args.commit, '--tier', 'all',
                 '--work-dir', str(output / 'downstream'), '--reuse-external-cache', '--copy-checkout-builds'],
                source, output / 'downstream.log', env, receipt)
            dependency = json.loads((output / 'downstream/result.json').read_text())
            if dependency.get('status') != 'passed' or dependency.get('resolved_commit') != args.commit:
                raise ValueError('Exact public Git installation did not pass')
        if tracked_snapshot(source, env) != initial:
            raise ValueError('Tracked release inputs changed while checks were running')
        if git(source, env, 'rev-parse', 'HEAD').decode().strip() != args.commit:
            raise ValueError('Checkout HEAD changed while checks were running')
        receipt.update(status='source-checks-passed-awaiting-downstream' if args.source_only else 'release-ready')
        return 0
    except (Exception, KeyboardInterrupt) as error:
        if receipt is not None:
            receipt.update(status='failed', error=str(error) or type(error).__name__)
        print(f'Release check failed: {error}', file=sys.stderr)
        return 1
    finally:
        if receipt is not None:
            receipt['finished_utc'] = now()
            save(output / 'result.json', receipt)
            print(json.dumps({key: receipt[key] for key in ('status', 'commit')}))


if __name__ == '__main__':
    raise SystemExit(main())
