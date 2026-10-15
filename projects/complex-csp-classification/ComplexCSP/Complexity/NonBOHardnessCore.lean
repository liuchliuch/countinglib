import ComplexCSP.Algebra.NonnegativeGramHardnessCore
import ComplexCSP.Complexity.NonBOToRealGram
import ComplexCSP.Complexity.CSPCommonField

/-! # Assembly of actual non-BO obstruction and Gram hardness reductions

The separate closed endpoint supplies the checked Potts foundation theorem.
-/
noncomputable section
open Classical
namespace ComplexCSP.ComplexityNonBOHardnessCore
open PlanarHom PlanarHom.Complexity AlgebraicProductInterpolation ComplexityReducedGram
variable {D : Type} [Fintype D] {s : ℕ} {L : Language D ℂ (Fin s)}

theorem witness_hard_of_potts (hPotts : RealLanguage.PositivePottsFoundation) (W : Witness L) :
    PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem W.input W.basis) := by
  obtain ⟨i,j,hm⟩ := RealGramField.strict_minor W
  have hh := NonnegativeGramHardnessCore.hard_of_potts (RealGramField.field W) (RealGramField.basis W) hPotts
    (RealGramField.matrix W) (RealGramField.matrix_nonnegative W) (RealGramField.matrix_symmetric W)
    W.factor W.factor_nonneg (RealGramField.matrix_gram W) i j hm
  exact hh.trans (RealGramReduction.reduction W)


/-- Supplied finite rational-basis realizations automatically have algebraic
complex entries; no independent algebraicity oracle is needed. -/
theorem realization_algebraic {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) (σ : K →+* ℂ) (M : Language D K (Fin s)) :
    ∀ i a,IsAlgebraic ℚ ((M.mapValues σ).value i a) := by
  letI : FiniteDimensional ℚ K := Module.Finite.of_basis basis
  intro i a
  exact (IsIntegral.map σ.toRatAlgHom (IsIntegral.of_finite (R := ℚ) (M.value i a))).isAlgebraic

/-- Arbitrary supplied coefficient fields are connected through an actual
finite common field; neither starting field must embed into the other. -/
theorem hard_of_not_jointBO_of_potts {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) (σ : K →+* ℂ) (M : Language D K (Fin s))
    (hPotts : RealLanguage.PositivePottsFoundation) (hnot : ¬JointBO (M.mapValues σ)) :
    PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem M basis) := by
  obtain ⟨W⟩ := ComplexityNonBOToGram.exists_reduced_gram (M.mapValues σ)
    (realization_algebraic basis σ M) hnot
  exact (witness_hard_of_potts hPotts W).trans
    (ComplexityCSPCommonField.reduction W.basis basis W.field.subtype σ W.input M W.input_correct)

end ComplexCSP.ComplexityNonBOHardnessCore
