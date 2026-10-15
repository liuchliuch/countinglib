import ComplexCSP.Algebra.NonnegativeGramHardness
import ComplexCSP.Complexity.NonBOHardnessCore

/-! # Literal failure of joint block orthogonality implies real counting hardness

Every witness field, matrix, nonnegative Gram factor, reduction and final exact
coefficient transport is constructed from the original algebraic language.
-/
noncomputable section
open Classical
namespace ComplexCSP.ComplexityNonBOHardness
open PlanarHom PlanarHom.Complexity ComplexityReducedGram
variable {D : Type} [Fintype D] {s : ℕ} {L : Language D ℂ (Fin s)}

/-- The actual original-input realization carried by every constructed
obstruction is hard in its exact rational-basis output encoding. -/
theorem witness_hard (W : Witness L) :
    PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem W.input W.basis) := by
  obtain ⟨i,j,hm⟩ := RealGramField.strict_minor W
  have hh := NonnegativeGramHardness.hard (RealGramField.field W) (RealGramField.basis W)
    (RealGramField.matrix W) (RealGramField.matrix_nonnegative W) (RealGramField.matrix_symmetric W)
    W.factor W.factor_nonneg (RealGramField.matrix_gram W) i j hm
  exact hh.trans (RealGramReduction.reduction W)

/-- No supplied hardness witness: one is constructed from literal non-BO. -/
theorem exists_hard_realization (L : Language D ℂ (Fin s))
    (hL : ∀ i a,IsAlgebraic ℚ (L.value i a)) (hnot : ¬JointBO L) :
    ∃ W : Witness L, PromisedSharpPHard
      (ComplexityCSPCountReduction.partitionProblem W.input W.basis) := by
  obtain ⟨W⟩ := ComplexityNonBOToGram.exists_reduced_gram L hL hnot
  exact ⟨W,witness_hard W⟩

/-- The literal structural-condition failure has the same actual hard realization. -/
theorem exists_hard_realization_of_not_conditions [Nonempty D] (L : Language D ℂ (Fin s))
    (hL : ∀ i a,IsAlgebraic ℚ (L.value i a)) (hnot : ¬CaiChenConditions L) :
    ∃ W : Witness L, PromisedSharpPHard
      (ComplexityCSPCountReduction.partitionProblem W.input W.basis) :=
  exists_hard_realization L hL (fun h => hnot ((structural_collapse L hL).mpr h))


/-- Closed hardness in any supplied finite rational-basis field representation.
The actual two-field coordinate transport is constructed through a common field;
no inclusion between the two original fields and no entry-algebraicity premise
is required. -/
theorem hard_of_not_jointBO {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) (σ : K →+* ℂ) (M : Language D K (Fin s))
    (hnot : ¬JointBO (M.mapValues σ)) :
    PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem M basis) :=
  ComplexityNonBOHardnessCore.hard_of_not_jointBO_of_potts basis σ M
    PlanarHom.AlgebraicProductInterpolation.RealLanguage.positivePottsFoundation hnot

/-- The same theorem stated against an explicitly named original complex language. -/
theorem hard_in_realization {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
    (basis : Module.Basis (Fin d) ℚ K) (σ : K →+* ℂ) (M : Language D K (Fin s))
    (hM : M.mapValues σ=L) (hnot : ¬JointBO L) :
    PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem M basis) := by
  apply hard_of_not_jointBO basis σ M
  simpa only [hM] using hnot

/-- Failure of the literal Cai–Chen conditions is hard in the prescribed exact
coefficient encoding, with all representation changes and machines accounted for. -/
theorem hard_of_not_conditions {K : Type} [Field K] [Algebra ℚ K] {d : ℕ} [Nonempty D]
    (basis : Module.Basis (Fin d) ℚ K) (σ : K →+* ℂ) (M : Language D K (Fin s))
    (hnot : ¬CaiChenConditions (M.mapValues σ)) :
    PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem M basis) := by
  apply hard_of_not_jointBO basis σ M
  intro hbo
  exact hnot ((structural_collapse (M.mapValues σ)
    (ComplexityNonBOHardnessCore.realization_algebraic basis σ M)).mpr hbo)

end ComplexCSP.ComplexityNonBOHardness
