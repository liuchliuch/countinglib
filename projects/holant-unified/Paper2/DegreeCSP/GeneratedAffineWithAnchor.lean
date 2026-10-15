import Paper2.DegreeCSP.GeneratedFullSupportAffine
import Paper2.DegreeCSP.GeneratedAffineMapSubstitution
import Paper2.DegreeCSP.BooleanGeneratedAffineSupport
import Paper2.Paper1ProvedCriteria
import Holant.ReedMuller.AffinePatching.ReconstructionSupport

/-! The proved affine support retraction is realized by an actual finite XOR
circuit. This extends the coefficient theorem to arbitrary supports without
assuming a free-variable representation or deleting its nonzero circuit scale. -/
namespace Paper2.DegreeCSP.GeneratedAffineWithAnchor
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem affine {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hk : 0<k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (a : AlgebraicComplex) (ha : a≠0)
    (hanchor : Generated F k (GeneratedHadamardUnary.anchor a))
    (hp0 : Generated F k (literalPin false)) (hp1 : Generated F k (literalPin true))
    (f : Signature AlgebraicComplex n) (hf : Generated F k f) : Affine f := by
  classical
  by_cases hzero : f=0
  · rw [hzero]
    exact affine_zero n
  have hex : ∃x,f x≠0 := by
    by_contra none
    apply hzero
    funext x
    by_contra h
    exact none ⟨x,h⟩
  obtain ⟨z,hz⟩ := hex
  have hx := BooleanGeneratedAffineSupport.generated_support_xor F hk hX hBO f hf
  have ht : ∀ x y z : Holant.Tractable.AffinePhase.Word n,
      f x≠0→f y≠0→f z≠0→f (Holant.Tractable.AffinePhase.xor
        (Holant.Tractable.AffinePhase.xor x y) z)≠0 := by
    intro x y z hx' hy hz'
    exact hx x hx' y hy z hz'
  obtain ⟨S,p,hp,hpne,hpfix,hS⟩ :=
    Holant.ReedMuller.AffinePatching.exists_support_retraction f z hz ht
  obtain ⟨c,hc,hG⟩ := GeneratedAffineSubstitution.generated_substitution_of_isAffineMap
    a ha hanchor hp0 hp1 f hf p hp
  have hscaled : Affine (fun x=>c*f (p x)) :=
    GeneratedFullSupportAffine.affine hBO a ha hanchor hp0 hp1 _ hG
      (fun x=>mul_ne_zero hc (hpne x))
  have hcoef : Affine (fun x=>f (p x)) := by
    have h := hscaled.scale c⁻¹
    have he : (fun x=>c⁻¹*(c*f (p x)))=(fun x=>f (p x)) := by
      funext x
      rw [←mul_assoc,inv_mul_cancel₀ hc,one_mul]
    rw [he] at h
    exact h
  apply (Paper1Proved.affine_iff f).mpr
  have hI := Holant.Tractable.affine_indicator S
  have hR := hI.mul ((Paper1Proved.affine_iff _).mp hcoef)
  have he : (fun x=>(if S.Holds x then (1 : AlgebraicComplex) else 0)*f (p x))=f := by
    funext x
    by_cases hfx:f x≠0
    · rw [ite_eq_left ((hS x).mpr hfx),one_mul,hpfix x hfx]
    · rw [ite_eq_right (fun hs=>hfx ((hS x).mp hs)),zero_mul]
      exact (not_ne_iff.mp hfx).symm
  rw [he] at hR
  exact hR

end
end Paper2.DegreeCSP.GeneratedAffineWithAnchor
