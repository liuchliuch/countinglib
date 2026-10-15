import Counting.Algorithm.Pfaffian.Program
import Counting.Algorithm.Pfaffian.Semantics
import Counting.Algorithm.Pfaffian.Evaluator
import Counting.Algorithm.Pfaffian.Examples
import Counting.Algorithm.Pfaffian.FiniteAlphabet

/-!
# Exact Pfaffian evaluator

Public API for first-nonzero elimination, signed-pairing correctness and exact
encoded runtime over a fixed finite-dimensional rational field. Internal source
modules and declarations are isolated under `PfaffianPort`.

The original TM2 FP model is exposed explicitly. F1's finite stack-alphabet
refinement is a separate obligation; see `notes/finite-alphabet.md`.
-/
