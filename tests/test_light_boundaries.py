"""The small imports must never acquire the complete classifier packages."""
import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location('counting_light_boundary_verifier', Path(__file__).resolve().parents[1] / 'scripts/verify.py')
VERIFY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFY)

class LightEntryBoundary(unittest.TestCase):
    def closure(self, package):
        graph = {'Counting': [], 'Counting.Algorithms': ['Generic.Helper'], 'Generic.Helper': []}
        sources = [{'module': 'Counting', 'package': 'countingComplexity'},
                   {'module': 'Counting.Algorithms', 'package': 'countingComplexity'},
                   {'module': 'Generic.Helper', 'package': package}]
        return VERIFY.light_closures('all', graph, sources, compiled=True)

    def test_planar_classifier_cannot_hide_behind_generic_module_name(self):
        with self.assertRaisesRegex(RuntimeError, 'Generic.Helper'):
            self.closure('countingPlanarClassification')

    def test_csp_classifier_cannot_hide_behind_generic_module_name(self):
        with self.assertRaisesRegex(RuntimeError, 'Generic.Helper'):
            self.closure('countingComplexCSPClassification')

    def test_existing_planar_algorithm_provider_is_allowed(self):
        result = self.closure('countingPlanarAlgorithms')
        self.assertEqual(result['Counting.Algorithms']['forbidden_modules'], [])
        self.assertIn('Generic.Helper', result['Counting.Algorithms']['local_modules'])

    def test_default_core_cannot_acquire_a_complete_classifier(self):
        graph = {'Counting': ['Generic.Helper'], 'Generic.Helper': []}
        sources = [{'module': 'Counting', 'package': 'countingComplexity'},
                   {'module': 'Generic.Helper', 'package': 'countingPlanarClassification'}]
        with self.assertRaisesRegex(RuntimeError, 'Counting reaches'):
            VERIFY.light_closures('core', graph, sources)

if __name__ == '__main__':
    unittest.main()
