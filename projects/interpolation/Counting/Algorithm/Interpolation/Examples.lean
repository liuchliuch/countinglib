import Counting.Algorithm.Interpolation.Cost
import Mathlib.Tactic.NormNum

/-! Rational clients and executable boundary cases. All theorem checks use the
kernel; no native decision procedure is used to prove a proposition. -/

namespace Counting.Algorithm.Interpolation.Examples

open Polynomial

/-- Three exact rational interpolation nodes. -/
def rationalNodes (i : Fin 3) : ℚ := i.val

/-- Samples of `3 X² + 2 X + 5` at the three nodes. -/
def quadraticSamples (i : Fin 3) : ℚ :=
  3 * rationalNodes i * rationalNodes i + 2 * rationalNodes i + 5

theorem rationalNodes_injective : Function.Injective rationalNodes := by
  intro i j h
  apply Fin.ext
  change (i.val : ℚ) = (j.val : ℚ) at h
  exact_mod_cast h

/-- A direct execution theorem for the rational client. -/
theorem quadratic_recovery : evaluate rationalNodes quadraticSamples = 3 := by
  norm_num [evaluate, recoveryProgram, denominatorProgram, Program.listSum,
    Program.listProduct, List.ofFn_succ, Program.eval, Fin.succAbove,
    rationalNodes, quadraticSamples]

/-- The executable duplicate checker accepts the distinct rational nodes. -/
theorem quadratic_checked : checkedRecover rationalNodes quadraticSamples = some 3 := by
  rw [checkedRecover_of_injective _ _ rationalNodes_injective, quadratic_recovery]

/-- A client using the abstract polynomial correctness theorem. -/
theorem rational_polynomial_client (P : Polynomial ℚ) (hP : P.natDegree ≤ 2) :
    evaluate rationalNodes (fun i => P.eval (rationalNodes i)) = P.coeff 2 :=
  evaluate_eq_coefficient rationalNodes rationalNodes_injective P hP

/-- The zero-degree case has one sample and no denominator factors. -/
theorem constant_client :
    evaluate (fun _ : Fin 1 => (7 : ℚ)) (fun _ => (-4 : ℚ)) = -4 := by
  simp

/-- A zero sample table is accepted and returns zero. -/
theorem zero_samples_client : checkedRecover rationalNodes (fun _ => 0) = some 0 := by
  simp [checkedRecover_of_injective _ _ rationalNodes_injective]

/-- Repeated nodes are rejected even when their samples agree. -/
theorem duplicate_nodes_client :
    checkedRecover (fun _ : Fin 2 => (0 : ℚ)) (fun _ => (5 : ℚ)) = none := by
  decide

/-- The measured interpreter reports the cost accumulated during execution. -/
theorem quadratic_measured :
    measuredRecover rationalNodes quadraticSamples = (3, ⟨3, 18⟩) := by
  apply Prod.ext
  · simpa using quadratic_recovery
  · have hq := measuredRecover_queries rationalNodes quadraticSamples
    have ho := measuredRecover_fieldOps rationalNodes quadraticSamples
    cases hc : (measuredRecover rationalNodes quadraticSamples).2
    simp_all

#eval checkedRecover rationalNodes quadraticSamples
#eval measuredRecover rationalNodes quadraticSamples
#eval checkedRecover (fun _ : Fin 1 => (7 : ℚ)) (fun _ => (-4 : ℚ))
#eval checkedRecover rationalNodes (fun _ => 0)
#eval checkedRecover (fun _ : Fin 2 => (0 : ℚ)) (fun _ => (5 : ℚ))

end Counting.Algorithm.Interpolation.Examples
