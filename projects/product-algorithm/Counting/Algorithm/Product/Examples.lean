import Counting.Algorithm.Product
import Mathlib.Data.Rat.Defs

/-! Executable clients exercise both elimination branches and the public S1 bridge.
The numerical proofs use kernel reduction (`decide`), not `native_decide`. -/

namespace Counting.Algorithm.Product.Examples

/-- A weighted parity component on three variables and a fourth isolated variable.
The unary at port 2 occurs twice; the final equality has a repeated port. -/
def weightedNat : Instance Nat := ⟨4,
  [scalar 3, unary 0 2 5, unary 1 7 11, equality 0 1, disequality 1 2,
   unary 2 13 17, unary 2 13 17, equality 2 2]⟩

theorem weightedNat_evaluate : evaluate weightedNat = 80046 := by decide +kernel
theorem weightedNat_run : run weightedNat = (80046, 23) := by decide +kernel
theorem weightedNat_partition : weightedNat.toOpenInstance.partition Empty.elim = 80046 := by
  exact (run_eq_partition weightedNat).symm.trans (congrArg Prod.fst weightedNat_run)

theorem weightedNat_bound : (run weightedNat).2 ≤ (2 * 4 + 1) * 8 + 2 * 4 :=
  run_operations_le weightedNat

/-- Rational coefficients, a nontrivial equality component, and a free unary. -/
def weightedRat : Instance Rat := ⟨3,
  [scalar (-3 / 2), unary 0 (1 / 3) (2 / 5), equality 0 1,
   unary 1 (7 / 2) (-5 / 3), unary 2 2 (-1)]⟩

theorem weightedRat_evaluate : evaluate weightedRat = -3 / 4 := by decide +kernel
theorem weightedRat_partition : weightedRat.partition = -3 / 4 :=
  (evaluate_eq_partition weightedRat).symm.trans weightedRat_evaluate

/-- Exact cancellation is valid in a ring; no nonzero intermediate is assumed. -/
def cancellation : Instance Rat := ⟨2, [unary 0 1 (-1), equality 0 1]⟩
theorem cancellation_partition : cancellation.partition = 0 := by
  rw [← evaluate_eq_partition]
  decide +kernel

/-- A contradictory parity cycle is rejected by elimination. -/
def oddCycle : Instance Nat := ⟨3, [equality 0 1, disequality 1 2, equality 2 0]⟩
theorem oddCycle_partition : oddCycle.partition = 0 := by
  rw [← evaluate_eq_partition]
  decide +kernel

/-- The self-disequality is retained; the other two variables remain explicit. -/
def selfDisequality : Instance Nat := ⟨3, [disequality 1 1]⟩
theorem selfDisequality_partition : selfDisequality.partition = 0 := by
  rw [← evaluate_eq_partition]
  decide +kernel

/-- Repeated nullary occurrences survive even when there are no variables. -/
def nullary : Instance Nat := ⟨0, [scalar 3, scalar 3, scalar 2]⟩
theorem nullary_partition : nullary.partition = 18 := by
  rw [← evaluate_eq_partition]
  decide +kernel

/-- Every explicitly represented isolated Boolean variable contributes two. -/
def isolated : Instance Nat := ⟨5, []⟩
theorem isolated_partition : isolated.partition = 32 := by
  rw [← evaluate_eq_partition]
  decide +kernel

def zeroScalar : Instance Rat := ⟨2, [scalar 0, unary 0 7 (-2)]⟩
theorem zeroScalar_partition : zeroScalar.partition = 0 := by
  rw [← evaluate_eq_partition]
  decide +kernel

end Counting.Algorithm.Product.Examples
