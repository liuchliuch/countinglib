import Counting.Algorithm.Interpolation.Cost
import Mathlib.Tactic.NormNum

/-! Recover the coefficient of X² from three rational samples. The measured
interpreter counts sample queries and field operations; node checking, program
construction, and the representation cost of rational arithmetic are separate. -/

namespace Counting.Tutorial.Interpolation

open Counting.Algorithm.Interpolation

def nodes (i : Fin 3) : ℚ := i.val

def samples (i : Fin 3) : ℚ := 3 * nodes i * nodes i + 2 * nodes i + 5

theorem nodes_injective : Function.Injective nodes := by
  intro i j h
  apply Fin.ext
  change (i.val : ℚ) = (j.val : ℚ) at h
  exact_mod_cast h

theorem recovered_coefficient : evaluate nodes samples = 3 := by
  norm_num [evaluate, recoveryProgram, denominatorProgram, Program.listSum,
    Program.listProduct, List.ofFn_succ, Program.eval, Fin.succAbove, nodes, samples]

theorem checked_result : checkedRecover nodes samples = some 3 := by
  rw [checkedRecover_of_injective _ _ nodes_injective, recovered_coefficient]

theorem measured_result : measuredRecover nodes samples = (3, ⟨3, 18⟩) := by
  apply Prod.ext
  · simpa using recovered_coefficient
  · have hq := measuredRecover_queries nodes samples
    have ho := measuredRecover_fieldOps nodes samples
    cases hc : (measuredRecover nodes samples).2
    simp_all

/-- The same nodes work for every polynomial satisfying the degree bound. -/
theorem degree_two_client (P : Polynomial ℚ) (hP : P.natDegree ≤ 2) :
    evaluate nodes (fun i => P.eval (nodes i)) = P.coeff 2 :=
  evaluate_eq_coefficient nodes nodes_injective P hP

theorem duplicate_nodes_rejected :
    checkedRecover (fun _ : Fin 2 => (0 : ℚ)) (fun _ => (5 : ℚ)) = none := by
  decide

end Counting.Tutorial.Interpolation
