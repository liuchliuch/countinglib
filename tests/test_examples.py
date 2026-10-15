"""Negative controls for the public example verification driver.

These unit tests exercise source selection, stability and receipt rejection.
Actual private/generated declaration and axiom enumeration is exercised by the
Lean Audit.lean self-test and by check_examples.py on the compiled tutorials.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / 'scripts/check_examples.py'
SPEC = importlib.util.spec_from_file_location('counting_check_examples', SCRIPT)
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)
PROJECT = next(parent for parent in Path(__file__).resolve().parents
               if (parent / 'scripts/verify.py').is_file())
VERIFY = CHECK.load_verifier(PROJECT)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class ExampleInputs(unittest.TestCase):
    def test_exact_scopes(self):
        self.assertEqual(len(CHECK.SCOPES['core']), 3)
        self.assertEqual(len(CHECK.SCOPES['all']), 7)
        self.assertEqual(set(CHECK.SCOPES['all']) - set(CHECK.SCOPES['core']),
                         {'Holant', 'ComplexCSP', 'PlanarHom', 'MatchgateWidth'})

    def test_missing_public_source_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(RuntimeError, 'Missing or symbolic-link'):
                CHECK.source_inventory(Path(directory), 'core', SimpleNamespace(sha=sha))

    def test_changed_or_deleted_source_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'Tutorial.lean'
            path.write_text('theorem example : True := True.intro\n')
            inventory = [{'path': path.name, 'sha256': sha(path)}]
            CHECK.assert_source_stability(root, inventory, SimpleNamespace(sha=sha))
            path.write_text('theorem example : False := by contradiction\n')
            with self.assertRaisesRegex(RuntimeError, 'source changed'):
                CHECK.assert_source_stability(root, inventory, SimpleNamespace(sha=sha))
            path.unlink()
            with self.assertRaisesRegex(RuntimeError, 'source changed'):
                CHECK.assert_source_stability(root, inventory, SimpleNamespace(sha=sha))

    def test_symlink_substitution_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'Tutorial.lean'
            path.write_text('theorem example : True := True.intro\n')
            inventory = [{'path': path.name, 'sha256': sha(path)}]
            path.rename(root / 'Other.lean')
            path.symlink_to('Other.lean')
            with self.assertRaisesRegex(RuntimeError, 'source changed'):
                CHECK.assert_source_stability(root, inventory, SimpleNamespace(sha=sha))

    def test_previous_receipt_is_archived(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out = root / 'validation/examples/core'
            out.mkdir(parents=True)
            (out / 'result.json').write_text('{"status":"passed","old":true}\n')
            archive = CHECK.archive_previous(root, out)
            self.assertEqual((root / archive / 'result.json').read_bytes(),
                             (out / 'result.json').read_bytes())

    def test_production_closure_is_exact(self):
        graph = {'docs.examples.T': ['Counting.Core'], 'Counting.Core': ['Counting.Shared'],
                 'Counting.Shared': ['Init'], 'Counting.Unused': []}
        def closure(roots, graph):
            pending, reached = list(roots), set()
            while pending:
                name = pending.pop()
                if name not in reached:
                    reached.add(name)
                    pending.extend(graph.get(name, []))
            return reached
        verify = SimpleNamespace(module_closure=closure)
        examples = [{'module': 'docs.examples.T'}]
        production = [{'module': name} for name in ('Counting.Core', 'Counting.Shared', 'Counting.Unused')]
        selected = CHECK.select_production_inputs(examples, production, graph, verify)
        self.assertEqual([source['module'] for source in selected], ['Counting.Core', 'Counting.Shared'])
        with self.assertRaisesRegex(RuntimeError, 'conflicts'):
            CHECK.select_production_inputs(examples, production + examples, graph, verify)


class ExampleAudit(unittest.TestCase):
    def make_ledger(self, directory):
        prefix = Path(directory) / 'audit'
        module = 'docs.examples.Fixture'
        summary = dict(status='passed', modules=1, declarations=1, theorems=1,
            external_export_declarations=0, audited_kernel_roots=1,
            compatible_repeated_source_exports=0,
            compiler_auxiliaries_without_kernel_declarations=0,
            local_axioms=0, disallowed_dependencies=0,
            external_export_disallowed_dependencies=0, observed_axioms=[],
            unsafe_declarations=0, partial_declarations=0)
        ledgers = {
            '-modules.jsonl': [dict(name=module, kernel_declarations=1,
                module_constant_names=1, module_extra_names=0,
                exported_kernel_entries=1, compiler_only_entries=0,
                exported_external_kernel_entries=0)],
            '-closure.jsonl': [dict(name=module, production_owned=True, imports=[])],
            '-declarations.jsonl': [dict(name='Counting.Tutorial.Fixture.witness',
                module=module, kind='theorem', axioms=[],
                type_representation='Lean.Expr structural hash', type_hash='1')],
            '-external-declarations.jsonl': [], '-reexports.jsonl': [],
            '-codegen.jsonl': [], '-axioms.jsonl': []}
        for suffix, values in ledgers.items():
            Path(str(prefix) + suffix).write_text(''.join(json.dumps(value) + '\n'
                                                      for value in values))
        Path(str(prefix) + '-summary.json').write_text(json.dumps(summary))
        return prefix, module, ledgers['-declarations.jsonl'][0]

    def test_existing_ledger_validator_rejects_forbidden_transitive_axiom(self):
        # This checks the trusted Python ledger validator, not Lean proof
        # enumeration. The separate actual Lean rejection fixture covers that.
        with tempfile.TemporaryDirectory() as directory:
            prefix, module, declaration = self.make_ledger(directory)
            args = (prefix, [{'module': module}], {module: []}, {module: []}, VERIFY)
            CHECK.validate_example_audit(*args)
            declaration['axioms'] = ['Lean.ofReduceBool']
            Path(str(prefix) + '-declarations.jsonl').write_text(json.dumps(declaration) + '\n')
            with self.assertRaisesRegex(RuntimeError, 'Disallowed local declaration/axiom'):
                CHECK.validate_example_audit(*args)

    def test_existing_ledger_validator_rejects_local_axiom(self):
        with tempfile.TemporaryDirectory() as directory:
            prefix, module, declaration = self.make_ledger(directory)
            declaration['kind'] = 'axiom'
            Path(str(prefix) + '-declarations.jsonl').write_text(json.dumps(declaration) + '\n')
            with self.assertRaisesRegex(RuntimeError, 'Disallowed local declaration/axiom'):
                CHECK.validate_example_audit(prefix, [{'module': module}], {module: []},
                                             {module: []}, VERIFY)

    def test_unsafe_and_partial_summaries_rejected(self):
        for field in ('unsafe_declarations', 'partial_declarations'):
            verify = SimpleNamespace(validate_audit=lambda *args: {'summary': {
                'unsafe_declarations': int(field == 'unsafe_declarations'),
                'partial_declarations': int(field == 'partial_declarations')}})
            with self.assertRaisesRegex(RuntimeError, 'unsafe or partial'):
                CHECK.validate_example_audit(Path('unused'), [], {}, {}, verify)

    def test_compiled_import_mismatch_rejected(self):
        verify = SimpleNamespace(validate_audit=lambda *args: {'summary': {
                'unsafe_declarations': 0, 'partial_declarations': 0}},
            records=lambda path: iter([{'name': 'docs.examples.T', 'imports': ['Wrong.Input']}]))
        with self.assertRaisesRegex(RuntimeError, 'imports differ'):
            CHECK.validate_example_audit(Path('unused'), [{'module': 'docs.examples.T'}],
                                         {}, {'docs.examples.T': ['Expected.Input']}, verify)

    def test_early_failure_invalidates_prior_passing_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out = root / 'validation/examples/core'
            out.mkdir(parents=True)
            prior = {'status': 'passed', 'old': True}
            (out / 'result.json').write_text(json.dumps(prior))
            def save_json(path, value):
                path.write_text(json.dumps(value))
            verify = SimpleNamespace(now=lambda: '2026-10-15T00:00:00Z', save_json=save_json,
                relative=lambda path: str(path.relative_to(root)), sha=sha)
            with patch.object(CHECK, 'source_inventory', side_effect=KeyboardInterrupt()):
                self.assertEqual(CHECK.check(root, 'core', 2, verify), 1)
            result = json.loads((out / 'result.json').read_text())
            self.assertEqual(result['status'], 'failed')
            self.assertEqual(result['error'], 'KeyboardInterrupt')
            self.assertIn('finished_utc', result)
            archived = json.loads((root / result['previous_evidence'] / 'result.json').read_text())
            self.assertEqual(archived, prior)


if __name__ == '__main__':
    unittest.main()
