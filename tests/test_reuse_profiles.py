"""The reuse profile must cover every new module and audit actual dependencies."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location(
    'reuse_profile_verifier', Path(__file__).resolve().parents[1] / 'scripts/verify.py')
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)


class ReuseProfileTests(unittest.TestCase):
    def setUp(self):
        self.configs = {
            'countingComplexity': {'lean_lib': [
                {'name': 'CountingReuse', 'roots': [], 'globs': ['Counting.Reuse']}]},
            'countingOpenNetworkBridge': {'lean_lib': [
                {'name': 'Bridge', 'roots': [], 'globs': ['Counting.Bridge.OpenNetwork.+']}]},
            'holantUnified': {'lean_lib': [
                {'name': 'Holant', 'roots': [], 'globs': ['Holant.OpenNetwork', 'Paper2.Test']}]},
        }
        self.sources = [
            {'module': 'Counting.Reuse', 'package': 'countingComplexity', 'library': 'CountingReuse'},
            {'module': 'Counting.Bridge.OpenNetwork.Clients',
             'package': 'countingOpenNetworkBridge', 'library': 'Bridge'},
            {'module': 'Holant.OpenNetwork', 'package': 'holantUnified', 'library': 'Holant'},
        ]
        self.graph = {
            '@acceptance': ['Counting.Reuse'],
            'Counting.Reuse': ['Counting.Bridge.OpenNetwork.Clients'],
            'Counting.Bridge.OpenNetwork.Clients': ['Holant.OpenNetwork'],
            'Holant.OpenNetwork': ['Mathlib.Data.Fintype.Basic'],
        }

    def test_canonical_dependencies_are_selected_with_new_modules(self):
        selected = verifier.select_scope('reuse', self.sources, self.graph, self.configs)
        self.assertEqual({row['module'] for row in selected},
                         {row['module'] for row in self.sources})

    def test_an_omitted_new_client_is_rejected(self):
        self.graph['Counting.Reuse'] = ['Holant.OpenNetwork']
        with self.assertRaisesRegex(RuntimeError, 'Acceptance omits'):
            verifier.select_scope('reuse', self.sources, self.graph, self.configs)

    def test_a_claimed_local_cache_without_source_is_rejected(self):
        self.graph['Counting.Bridge.OpenNetwork.Clients'].append(
            'Counting.Bridge.OpenNetwork.Missing')
        with self.assertRaisesRegex(RuntimeError, 'has no owned source'):
            verifier.select_scope('reuse', self.sources, self.graph, self.configs)

    def test_classification_dependencies_cannot_enter_reuse_profile(self):
        self.sources.append({'module': 'Paper2.Test', 'package': 'holantUnified', 'library': 'Holant'})
        self.graph['Counting.Bridge.OpenNetwork.Clients'].append('Paper2.Test')
        self.graph['Paper2.Test'] = []
        with self.assertRaisesRegex(RuntimeError, 'paper/classification'):
            verifier.select_scope('reuse', self.sources, self.graph, self.configs)


if __name__ == '__main__':
    unittest.main()
