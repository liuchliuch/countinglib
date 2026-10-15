import Paper2.RelativeEO.Paper1BinaryAccepted
import Paper2.RelativeEO.BinaryEOForm

/-! The entire arity-two case of Paper 2 Lemma 3.9: singular EO binaries give
actual unary factors; infinite projective order uses only exact Paper 1 3.1;
finite projective order has the independently proved algebraic ARS witness. -/
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup

/-- Algebraic projective ARS, in the source's inverse-scalar convention. -/
def ProjectiveARS {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  ∃ c : AlgebraicComplex, c ≠ 0 ∧ ∀ x,
    (c : ℂ)⁻¹ * (f x : ℂ) = star ((c : ℂ)⁻¹ * (f (fun i => !(x i)) : ℂ))

theorem binary_eo_alternative (P : Paper1BinaryInterpolationAccepted)
    (F : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted) (L : Language)
    (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (f : Signature AlgebraicComplex 2)
    (hf : f ≠ 0) (hEO : Signature.CentralSupport f)
    (hmem : (⟨2, f⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ProjectiveARS f ∨ SharpPHard .nativeX L := by
  classical
  let a := f (binWord false true)
  let b := f (binWord true false)
  have hform : f = eoSignature a b := binary_central_form f hEO
  have hside : ¬ CommonOneSided L.family := by
    intro hs
    obtain ⟨⟨g, hg, x, hx, hneg⟩, ⟨h, hh, y, hy, hpos⟩⟩ := hboth
    rcases hs with hs | hs
    · exact (not_le_of_gt hneg) (hs g hg x hx)
    · exact (not_le_of_gt hpos) (hs h hh y hy)
  have heomem : (⟨2, eoSignature a b⟩ : AnySignature AlgebraicComplex) ∈ L.family := hform ▸ hmem
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      apply hf
      rw [hform, ha, hb, eoSignature_zero]
    right
    have hfactor : (⟨2, Signature.tensor (pinAmplitude true b) (TensorDecomposition.literalPin false)⟩ :
        AnySignature AlgebraicComplex) ∈ L.family := by
      simpa only [ha, eoSignature_left_zero] using heomem
    exact rankOne_binary_hard F U L hpre hside hnot _ _ (pinAmplitude_ne_zero true b hb)
      (TensorDecomposition.literalPin_ne_zero false) hfactor
  · by_cases hb : b = 0
    · right
      have hfactor : (⟨2, Signature.tensor (pinAmplitude false a) (TensorDecomposition.literalPin true)⟩ :
          AnySignature AlgebraicComplex) ∈ L.family := by
        simpa only [hb, eoSignature_right_zero] using heomem
      exact rankOne_binary_hard F U L hpre hside hnot _ _ (pinAmplitude_ne_zero false a ha)
        (TensorDecomposition.literalPin_ne_zero true) hfactor
    · by_cases hfinite : ProjectivelyFinite (transfer (eoMatrix a b))
      · left
        rw [hform]
        exact eo_finite_order_ars a b ha hb hfinite
      · right
        apply infinite_transfer_hard P F U L hpre hboth hnot (eoMatrix a b) heomem _ hfinite
        rw [eo_transfer, Matrix.det_diagonal]
        simpa [Fintype.prod_bool] using mul_ne_zero hb ha

end Paper2.RelativeEO
