import Counting.Algorithm.Interpolation.Algorithm
import Mathlib.Tactic.Ring

/-!
# Arithmetic cost and division safety

All counts below are derived from the syntax-directed recursions in `Program`.
Constants and list construction are free in this field-operation model. The
checked front end's finite equality comparisons and all representation/bit costs
are separate from these counts.
-/

namespace Counting.Algorithm.Interpolation

open scoped BigOperators

variable {K : Type*} [Field K] {m : ℕ}

@[simp] theorem denominatorProgram_queries (nodes : Fin (m + 1) → K)
    (i : Fin (m + 1)) : (denominatorProgram nodes i).queries = 0 := by
  simp [denominatorProgram, List.map_ofFn, List.sum_ofFn]

@[simp] theorem denominatorProgram_fieldOps (nodes : Fin (m + 1) → K)
    (i : Fin (m + 1)) : (denominatorProgram nodes i).fieldOps = 2 * m := by
  simp [denominatorProgram, List.map_ofFn, List.sum_ofFn]
  omega

/-- Exactly one query is charged for each of the `m + 1` samples. -/
@[simp] theorem recoveryProgram_queries (nodes : Fin (m + 1) → K) :
    (recoveryProgram nodes).queries = m + 1 := by
  simp [recoveryProgram, List.map_ofFn, List.sum_ofFn, Nat.add_comm]

/-- The concrete program uses exactly `2(m + 1)^2` field operations. -/
@[simp] theorem recoveryProgram_fieldOps (nodes : Fin (m + 1) → K) :
    (recoveryProgram nodes).fieldOps = 2 * (m + 1) ^ 2 := by
  simp [recoveryProgram, List.map_ofFn, List.sum_ofFn]
  ring

/-- Polynomial arithmetic-operation bound, with the size parameter `m + 1`. -/
theorem recoveryProgram_fieldOps_le (nodes : Fin (m + 1) → K) :
    (recoveryProgram nodes).fieldOps ≤ 2 * (m + 1) ^ 2 := by
  rw [recoveryProgram_fieldOps]

/-- Denominator products themselves contain no divisions. -/
@[simp] theorem denominatorProgram_safe (nodes values : Fin (m + 1) → K)
    (i : Fin (m + 1)) : (denominatorProgram nodes i).Safe values := by
  simp [denominatorProgram]

/-- Distinct nodes certify every division executed by the recovery program. -/
theorem recoveryProgram_safe (nodes values : Fin (m + 1) → K)
    (hi : Function.Injective nodes) : (recoveryProgram nodes).Safe values := by
  simp [recoveryProgram, interpolationDenominator_ne_zero nodes hi]

/-- Execute while measuring actual traversed query and arithmetic nodes. -/
def measuredRecover (nodes values : Fin (m + 1) → K) : K × Program.Cost :=
  (recoveryProgram nodes).run values

@[simp] theorem measuredRecover_value (nodes values : Fin (m + 1) → K) :
    (measuredRecover nodes values).1 = evaluate nodes values := by
  simp [measuredRecover, evaluate]

@[simp] theorem measuredRecover_queries (nodes values : Fin (m + 1) → K) :
    (measuredRecover nodes values).2.queries = m + 1 := by
  simp [measuredRecover]

@[simp] theorem measuredRecover_fieldOps (nodes values : Fin (m + 1) → K) :
    (measuredRecover nodes values).2.fieldOps = 2 * (m + 1) ^ 2 := by
  simp [measuredRecover]

/-- One client-facing theorem packages correctness, exact measured cost, and
nonzero denominators, without making a bit-time or machine-model claim. -/
theorem measuredRecover_spec (nodes : Fin (m + 1) → K)
    (hi : Function.Injective nodes) (P : Polynomial K) (hP : P.natDegree ≤ m) :
    (measuredRecover nodes (fun i => P.eval (nodes i))).1 = P.coeff m ∧
    (measuredRecover nodes (fun i => P.eval (nodes i))).2.queries = m + 1 ∧
    (measuredRecover nodes (fun i => P.eval (nodes i))).2.fieldOps = 2 * (m + 1) ^ 2 ∧
    (recoveryProgram nodes).Safe (fun i => P.eval (nodes i)) := by
  exact ⟨by rw [measuredRecover_value, evaluate_eq_coefficient nodes hi P hP],
    measuredRecover_queries _ _, measuredRecover_fieldOps _ _, recoveryProgram_safe _ _ hi⟩

/-- An empty list of denominator factors is the correct degree-zero case. -/
@[simp] theorem evaluate_degree_zero (nodes values : Fin 1 → K) :
    evaluate nodes values = values 0 := by
  simp [evaluate_eq_recoverTop, recoverTop, interpolationDenominator]

/-- Zero samples produce zero, independently of the nodes. -/
@[simp] theorem evaluate_zero_samples (nodes : Fin (m + 1) → K) :
    evaluate nodes (fun _ => 0) = 0 := by
  simp [evaluate_eq_recoverTop, recoverTop]

/-- The zero polynomial is covered for every degree bound, including zero. -/
@[simp] theorem evaluate_zero_polynomial (nodes : Fin (m + 1) → K) :
    evaluate nodes (fun i => (0 : Polynomial K).eval (nodes i)) = 0 := by
  simp

end Counting.Algorithm.Interpolation
