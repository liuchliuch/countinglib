import Paper2.DegreeCSP.GeneratedHadamardUnary
import Paper2.DegreeCSP.GeneratedPhaseRemoval
import Paper2.DegreeCSP.GeneratedSignQuadratic
import Paper2.DegreeCSP.FourthRootAxisAffine

/-! Full-support classification with an actual scaled Hadamard anchor. Every
coordinate unary, phase-removal product and offending cube Gram is physically
degree-generated, and all nonzero scalars are preserved in the proof. -/
namespace Paper2.DegreeCSP.GeneratedFullSupportAffine
open Tractable TensorDecomposition AxisRatioSigns
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem affine {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (a : AlgebraicComplex) (ha : a≠0)
    (hA : Generated F k (GeneratedHadamardUnary.anchor a))
    (hp0 : Generated F k (literalPin false)) (hp1 : Generated F k (literalPin true))
    (f : Signature AlgebraicComplex n) (hf : Generated F k f) (hne : ∀x,f x≠0) :
    Affine f := by
  have h4 := GeneratedHadamardUnary.axis_phase_four hBO a ha hA f hf hp0 hne
  have h8 (i : Fin n) : axisRatio f i^8=1 := by
    calc
      axisRatio f i^8=(axisRatio f i^4)^2 := by ring
      _=1 := by rw [h4 i]; norm_num
  obtain ⟨P,c,hc,_,hG,hform⟩ := GeneratedPhaseRemoval.signs hBO f hf hp0 hne h8
  have hcc : (c : ℂ)≠0 := by exact_mod_cast hc
  have hquad : BooleanQuadratic.Quadratic (fun x=>bitValue (ZMod 2) (P x)) := by
    apply GeneratedSignQuadratic.quadratic hBO _ hG hp0 hp1 (c : ℂ) hcc
    intro x
    cases hpx : P x <;> simp [bitValue,BadCubeGram.sign,hpx]
  exact FourthRootAxisAffine.affine_of_displayed f (f zeroWord) (axisRatio f) P h4 hquad hform

end
end Paper2.DegreeCSP.GeneratedFullSupportAffine
