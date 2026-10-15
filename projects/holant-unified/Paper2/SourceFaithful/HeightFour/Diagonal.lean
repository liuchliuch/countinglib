import Paper2.ReedMullerNormalization.AlgebraicRoot
import Paper2.SourceFaithful.LocalInputs
import Paper2.BellReduction.ChargeBoundary

/-! The legal whole-family endpoint normalization in the algebraic field.
The edge multiplier is exactly one, and support/half-charge are retained. -/
namespace Paper2.SourceFaithful.HeightFour
open Tractable ExactInput ReedMullerNormalization BellReduction

noncomputable def diagonalBasis (s : AlgebraicComplex) (hs : s ≠ 0) : InvertibleKernel where
  matrix := diagonal s
  inverse := diagonal s⁻¹
  matrix_inverse := by
    funext a b
    cases a <;> cases b <;>
      simp [Kernel.mul_apply,diagonal,Signature.equality,hs]
  inverse_matrix := by
    funext a b
    cases a <;> cases b <;>
      simp [Kernel.mul_apply,diagonal,Signature.equality,hs]

theorem diagonalBasis_conformal (s : AlgebraicComplex) (hs : s ≠ 0) :
    XConformal (diagonalBasis s hs) := by
  refine ⟨1,one_ne_zero,?_⟩
  simpa only [Kernel.pullback,diagonalBasis,Bell.X_eq_disequality,one_mul] using
    diagonal_preserves_X s hs

theorem diagonalBasis_highCharge (s : AlgebraicComplex) (hs : s ≠ 0)
    (F : SignatureFamily AlgebraicComplex) (hF : HighCharge F) :
    HighCharge (familyAction (diagonalBasis s hs) F) := by
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨(hF f hf).1,?_⟩
  intro x hx
  apply (hF f hf).2 x
  intro hz
  apply hx
  change Signature.coordinateAction (fun _ => diagonal s) f.2 x = 0
  rw [diagonal_action,hz,mul_zero]

/-- A normalized complete RM mountain gives a literal RM8 member after one
global legal basis action. Both actual machine reductions are retained. -/
theorem canonical_normalization
    (N : Paper1NormalizationAccepted) (L : Language)
    (hpre : Preprocessed L.family) (hHigh : HighCharge L.family)
    (hnot : ¬ Tract (kImage L)) (A B c : AlgebraicComplex)
    (hA : A ≠ 0) (hc : c ≠ 0) (hAB : A * B = c ^ 2)
    (hmem : (⟨8,source A B c⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ M : Language, HighCharge M.family ∧ ¬ Tract (kImage M) ∧
      (⟨8,fun x => c * ReedMuller.core x⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  obtain ⟨s,hs,hs8⟩ := exists_algebraic_normalizing_root A c hA hc
  let D := diagonalBasis s hs
  obtain ⟨M,hM,hML,hLM⟩ := N.normalize L hpre D (diagonalBasis_conformal s hs)
  have hcore : D.action (source A B c) = fun x => c * ReedMuller.core x :=
    diagonal_normalization A B c s hA hc hAB hs8
  refine ⟨M,?_,?_,?_,hML,hLM⟩
  · rw [hM]
    exact diagonalBasis_highCharge s hs L.family hHigh
  · intro ht
    apply hnot
    change Tract (familyAction sourceKBasis L.family)
    apply (xConformal_tract_iff (diagonalBasis_conformal s hs) L.family).mpr
    simpa only [kImage,hM] using ht
  · rw [hM]
    exact ⟨⟨8,source A B c⟩,hmem,by simp only [hcore]⟩

end Paper2.SourceFaithful.HeightFour
