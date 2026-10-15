import Counting.Flagships.PlanarHom
import Mathlib.Tactic.NormNum

/-!
# A fixed two-colour planar homomorphism problem

The matrix is `[[1, 2], [2, 4]]`, with unit vertex weights and no unary labels.
We prove its positive rank-one block form and invoke the closed Theorem 1.1.
The conclusion is the source model's exact fixed-language bit-machine contract
on promised ordinary planar multigraph inputs, including loops, parallel edges,
and isolated vertices. It does not assert a uniform algorithm for input matrices.
-/

namespace Counting.Tutorial.PlanarHom

noncomputable section

open _root_.PlanarHom
open AlgebraicProductInterpolation Structures

/-- The two positive rank-one factors are 1 and 2. -/
def amplitude (i : Fin 2) : ℝ := i.val + 1

def twoColour : RealLanguage 2 1 0 where
  matrices := fun _ i j => amplitude i * amplitude j
  unaries := Fin.elim0
  weights := fun _ => 1
  matrices_algebraic := by
    intro _ i j
    exact ((isAlgebraic_natCast i.val).add isAlgebraic_one).mul
      ((isAlgebraic_natCast j.val).add isAlgebraic_one)
  unaries_algebraic := fun l => Fin.elim0 l
  weights_algebraic := fun _ => isAlgebraic_one

theorem matrix_entries :
    twoColour.matrices 0 0 0 = 1 ∧ twoColour.matrices 0 0 1 = 2 ∧
    twoColour.matrices 0 1 0 = 2 ∧ twoColour.matrices 0 1 1 = 4 := by
  norm_num [twoColour, amplitude]

theorem amplitude_positive (i : Fin 2) : 0 < amplitude i := by
  unfold amplitude
  positivity

/-- One positive block, with no Ising coordinates (`d = 0`). -/
theorem structural_membership : NonnegativeClass (twoColour.matrices 0) := by
  classical
  refine ⟨1, fun _ => 0, ?_, ?_, ?_⟩
  · intro r
    exact ⟨0, Subsingleton.elim _ _⟩
  · intro i j hij
    exact (hij rfl).elim
  · intro r
    have hr : r = 0 := Subsingleton.elim _ _
    subst r
    let e : {i : Fin 2 // (0 : Fin 1) = 0} ≃ Fin 2 × Boolean.Cube 0 :=
      (Equiv.subtypeUnivEquiv (fun _ => rfl)).trans
        (Equiv.prodUnique (Fin 2) (Boolean.Cube 0)).symm
    exact .positive 2 0 (by decide) amplitude (Fin.elim0)
      amplitude_positive (fun i => Fin.elim0 i) e (by
        intro i j
        simp [twoColour, e, Boolean.tensor])

/-- A genuine theorem application: this fixed planar evaluation problem has
an exact polynomial-time bit machine, with its original input/output promises. -/
theorem fixed_planar_evaluation_inFP : twoColour.problem.InFP := by
  apply (MainDichotomyScope.theorem11 twoColour (fun _ => rfl) ?_ ?_).1
    structural_membership
  · intro i j
    exact mul_comm _ _
  · intro i j
    exact mul_nonneg (amplitude_positive i).le (amplitude_positive j).le

end

end Counting.Tutorial.PlanarHom
