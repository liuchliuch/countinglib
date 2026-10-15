"""Failures before any Lean invocation must invalidate the current self-test receipt."""
import importlib.util
import json
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('counting_verify', Path(__file__).resolve().parents[1] / 'scripts/verify.py')
VERIFY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFY)


class SelfTestReceipt(unittest.TestCase):
    def check_failure(self, failure):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            receipt = root / 'validation/selftest/result.json'
            receipt.parent.mkdir(parents=True)
            receipt.write_text(json.dumps({'status': 'passed', 'prior': True}))
            with patch.object(VERIFY, 'ROOT', root), patch.object(VERIFY, 'self_test_checks', side_effect=failure), patch.object(VERIFY, 'run') as run:
                self.assertEqual(VERIFY.self_test(SimpleNamespace(workers=2)), 1)
                run.assert_not_called()
            result = json.loads(receipt.read_text())
            self.assertEqual(result['status'], 'failed')
            self.assertIn('finished_utc', result)
            archived = root / result['previous_evidence'] / 'result.json'
            self.assertEqual(json.loads(archived.read_text()), {'status': 'passed', 'prior': True})

    def test_assertion_failure_replaces_prior_pass(self):
        self.check_failure(AssertionError('negative control rejected'))

    def test_interrupt_replaces_prior_pass(self):
        self.check_failure(KeyboardInterrupt())

    def test_unexpected_exception_replaces_prior_pass(self):
        self.check_failure(TypeError('unexpected fixture type'))

    def test_comparison_skips_a_failed_retry(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for stamp, status in [('20260101', 'passed'), ('20260102', 'passed'), ('20260103', 'failed')]:
                evidence = root / 'validation/history' / ('all-' + stamp)
                evidence.mkdir(parents=True)
                (evidence / 'result.json').write_text(json.dumps({'status': status}))
                (evidence / 'sources.json').write_text('[]')
                (evidence / 'audit-closure.jsonl').write_text('')
            with patch.object(VERIFY, 'ROOT', root):
                self.assertEqual(VERIFY.last_passed_baseline('all', 'validation/history/all-20260103'),
                                 'validation/history/all-20260102')
                self.assertIsNone(VERIFY.last_passed_baseline('core', None))


if __name__ == '__main__':
    unittest.main()
