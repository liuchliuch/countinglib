"""Exercise real isolated process groups without starting Lean or Lake."""
import importlib.util
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('verify_processes', Path(__file__).resolve().parents[1] / 'scripts/verify.py')
verify = importlib.util.module_from_spec(spec); spec.loader.exec_module(verify)

# The child ignores TERM; the leader uses the default TERM behavior.
PARENT = r'''
import os,signal,sys,time
from pathlib import Path
pid=os.fork()
if pid == 0:
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    Path(sys.argv[1]).write_text(str(os.getpid()))
    while True: time.sleep(0.02)
while True: time.sleep(0.02)
'''


def await_child(path):
    until = time.monotonic() + 5
    while time.monotonic() < until:
        if path.exists() and path.read_text(): return int(path.read_text())
        time.sleep(0.01)
    raise AssertionError('Isolated child did not become ready')


def stopped(pid):
    result = subprocess.run(['ps', '-o', 'stat=', '-p', str(pid)], capture_output=True, text=True)
    return result.returncode != 0 or not result.stdout.strip() or result.stdout.strip().startswith('Z')


@unittest.skipUnless(hasattr(os, 'fork') and hasattr(os, 'killpg'), 'POSIX process-group contract')
class ProcessTests(unittest.TestCase):
    def test_normal_exit_preserves_output_and_command_status(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); commands = []
            with patch.object(verify, 'ROOT', root):
                output = verify.run([sys.executable, '-c', 'print("actual output")'], root/'run.log', dict(os.environ), commands)
            self.assertEqual(output, 'actual output\n')
            self.assertEqual(commands[0]['exit_code'], 0)

    def test_failed_exit_records_real_code_and_log(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); commands = []
            with patch.object(verify, 'ROOT', root), self.assertRaisesRegex(RuntimeError, 'Command failed'):
                verify.run([sys.executable, '-c', 'print("failure"); raise SystemExit(3)'], root/'run.log', dict(os.environ), commands)
            self.assertEqual(commands[0]['exit_code'], 3)
            self.assertEqual((root/'run.log').read_text(), 'failure\n')

    def test_term_exited_leader_does_not_leave_ignoring_child(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory)/'child'
            process = subprocess.Popen([sys.executable, '-c', PARENT, str(marker)], start_new_session=True)
            try:
                child = await_child(marker)
                verify.terminate_process_group(process, 0.5)
                self.assertEqual(process.returncode, -signal.SIGTERM)
                until = time.monotonic() + 3
                while not stopped(child) and time.monotonic() < until: time.sleep(0.01)
                self.assertTrue(stopped(child), 'Ignoring descendant survived group cleanup')
            finally:
                try: os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError: pass
                process.wait()

    def test_run_interrupt_cleans_real_descendant_and_records_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); marker = root/'child'; commands = []; spawned = []; real_popen = subprocess.Popen
            def spawn(*args, **kwargs):
                process = real_popen(*args, **kwargs); spawned.append(process)
                real_wait = process.wait; first = True
                def interrupt_once(*a, **kw):
                    nonlocal first
                    if first:
                        first = False; await_child(marker); raise KeyboardInterrupt()
                    return real_wait(*a, **kw)
                process.wait = interrupt_once
                return process
            try:
                with patch.object(verify, 'ROOT', root), patch.object(verify.subprocess, 'Popen', side_effect=spawn):
                    with self.assertRaises(KeyboardInterrupt):
                        verify.run([sys.executable, '-c', PARENT, str(marker)], root/'run.log', dict(os.environ), commands)
                self.assertTrue(commands[0]['interrupted'])
                self.assertEqual(commands[0]['exit_code'], -signal.SIGTERM)
                child = int(marker.read_text()); until = time.monotonic()+3
                while not stopped(child) and time.monotonic() < until: time.sleep(0.01)
                self.assertTrue(stopped(child))
            finally:
                for process in spawned:
                    try: os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError: pass
                    process.wait()


if __name__ == '__main__': unittest.main()
