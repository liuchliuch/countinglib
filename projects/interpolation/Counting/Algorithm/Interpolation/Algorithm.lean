import Counting.Algorithm.Interpolation.Core
import Counting.Algorithm.Interpolation.Program
import Mathlib.Algebra.BigOperators.Fin

/-!
# Executable Lagrange recovery and its operation count

The program is built by two finite list folds. For each node, `Fin.succAbove`
enumerates exactly the other nodes; its product contains no self-difference.
The outer sum makes one sample query per node. Counts are inherited from the
independent syntax-directed `Program` semantics, not assigned to this algorithm.
-/

namespace Counting.Algorithm.Interpolation

open scoped BigOperators

variable {K : Type*} [Field K] {m : ℕ}

/-- A list-fold program computing the denominator at a node. -/
def denominatorProgram (nodes : Fin (m + 1) → K) (i : Fin (m + 1)) :
    Program K (Fin (m + 1)) :=
  Program.listProduct (List.ofFn fun j : Fin m =>
    Program.sub (Program.constant (nodes i)) (Program.constant (nodes (i.succAbove j))))

/-- A list-fold recovery program, with exactly one query for each sample. -/
def recoveryProgram (nodes : Fin (m + 1) → K) : Program K (Fin (m + 1)) :=
  Program.listSum (List.ofFn fun i =>
    Program.div (Program.query i) (denominatorProgram nodes i))

/-- Execute the program using the supplied sample oracle. -/
def evaluate (nodes values : Fin (m + 1) → K) : K :=
  (recoveryProgram nodes).eval values

/-- Reject repeated nodes before evaluating any recovery arithmetic. -/
def checkedRecover [DecidableEq K] (nodes values : Fin (m + 1) → K) : Option K :=
  if Function.Injective nodes then some (evaluate nodes values) else none

private theorem prod_succAbove_eq (f : Fin (m + 1) → K) (i : Fin (m + 1)) :
    (∏ j : Fin m, f (i.succAbove j)) = ∏ j ∈ Finset.univ.erase i, f j := by
  conv_rhs => rw [Fin.univ_succAbove m i]
  simp

@[simp] theorem denominatorProgram_eval (nodes values : Fin (m + 1) → K)
    (i : Fin (m + 1)) :
    (denominatorProgram nodes i).eval values = interpolationDenominator nodes i := by
  simp only [denominatorProgram, Program.eval_listProduct, List.map_ofFn,
    List.prod_ofFn]
  exact prod_succAbove_eq (fun j => nodes i - nodes j) i

@[simp] theorem recoveryProgram_eval (nodes values : Fin (m + 1) → K) :
    (recoveryProgram nodes).eval values = recoverTop nodes values := by
  simp only [recoveryProgram, Program.eval_listSum, List.map_ofFn, Function.comp_apply, Program.eval,
    denominatorProgram_eval, List.sum_ofFn, recoverTop]

/-- The executable list-fold evaluator implements the mathematical formula. -/
theorem evaluate_eq_recoverTop (nodes values : Fin (m + 1) → K) :
    evaluate nodes values = recoverTop nodes values := recoveryProgram_eval nodes values

/-- Executable recovery is correct for every polynomial of degree at most `m`. -/
theorem evaluate_eq_coefficient (nodes : Fin (m + 1) → K)
    (hi : Function.Injective nodes) (P : Polynomial K) (hP : P.natDegree ≤ m) :
    evaluate nodes (fun i => P.eval (nodes i)) = P.coeff m := by
  rw [evaluate_eq_recoverTop, recoverTop_eq_coefficient nodes hi P hP]

@[simp] theorem checkedRecover_of_injective [DecidableEq K]
    (nodes values : Fin (m + 1) → K) (hi : Function.Injective nodes) :
    checkedRecover nodes values = some (evaluate nodes values) := by
  simp [checkedRecover, hi]

@[simp] theorem checkedRecover_of_not_injective [DecidableEq K]
    (nodes values : Fin (m + 1) → K) (hi : ¬Function.Injective nodes) :
    checkedRecover nodes values = none := by
  simp [checkedRecover, hi]

/-- A concrete repeated pair is rejected, regardless of the samples. -/
theorem checkedRecover_duplicate [DecidableEq K] (nodes values : Fin (m + 1) → K)
    (i j : Fin (m + 1)) (hne : i ≠ j) (heq : nodes i = nodes j) :
    checkedRecover nodes values = none := by
  apply checkedRecover_of_not_injective
  intro hi
  exact hne (hi heq)

/-- The checked API returns the correct coefficient on valid interpolation nodes. -/
theorem checkedRecover_eq_coefficient [DecidableEq K] (nodes : Fin (m + 1) → K)
    (hi : Function.Injective nodes) (P : Polynomial K) (hP : P.natDegree ≤ m) :
    checkedRecover nodes (fun i => P.eval (nodes i)) = some (P.coeff m) := by
  rw [checkedRecover_of_injective nodes _ hi, evaluate_eq_coefficient nodes hi P hP]

end Counting.Algorithm.Interpolation
