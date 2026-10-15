import Paper2.DegreeCSP.GeneratedCodeSevenFromAnchor
import Paper2.DegreeCSP.FullSupportAnchorSelection
import Paper2.DegreeCSP.GeneratedAffineWithAnchor
import Paper2.DegreeCSP.NoAnchorComplete
import Paper2.DegreeCSP.NoAnchorGeneratedCodeMask

/-! Concrete affine and support-mask resources from actual degree-generated
block orthogonality. A full-support nonproduct table produces a genuine
Hadamard anchor; all subsequent circuits and scalars are proved internally. -/
namespace Paper2.DegreeCSP.AllBOAffineResources
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem of_full_support_nonproduct {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hk : 0<k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (f : Signature AlgebraicComplex n) (hf : Generated F k f)
    (hne : ∀x,f x≠0) (hnot : ¬Product f) :
    (∀{m}(g : Signature AlgebraicComplex m),Generated F k g→Affine g) ∧
      ∃c : AlgebraicComplex,c≠0 ∧
        Generated F k (fun y=>c*GeneratedCodeSeven.indicator y) := by
  have hp0 := generated_literalPin hk false h0
  have hp1 := generated_literalPin hk true h1
  obtain ⟨a,ha,hanchor⟩ := FullSupportAnchorSelection.exists_anchor hBO hp0 hp1 f hf hne hnot
  refine ⟨?_,GeneratedCodeSevenFromAnchor.exists_scaled_code a ha hanchor⟩
  intro m g hg
  exact GeneratedAffineWithAnchor.affine hk hX hBO a ha hanchor hp0 hp1 g hg

/-- Actual BO and exclusion from the unchanged source tract criterion supply
both resources. The product alternative is eliminated internally, and the
remaining cases construct their own literal support mask. -/
theorem resources (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    {k : ℕ} (hk : 2≤k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (hnot : ¬Tract (familyAction sourceKBasis F)) :
    (∀{n}(f : Signature AlgebraicComplex n),Generated F k f→Affine f) ∧
      ∃c : AlgebraicComplex,c≠0 ∧
        Generated F k (fun y=>c*GeneratedCodeSeven.indicator y) := by
  classical
  by_cases hno : NoAnchorWeightedSupport.AllFullSupportProduct F k
  · have hproduct : ¬(∀f∈F,Product f.2) := fun hp=>hnot
      (ClassesToTract.product_family F hF hp)
    refine ⟨?_,NoAnchorGeneratedCodeMask.exists_scaled_code F hk hX h0 h1 hBO hno hproduct⟩
    intro n f hf
    exact NoAnchorComplete.generated_affine_of_not_tract F hF hk hX h0 h1 hBO hno hnot n f hf
  · unfold NoAnchorWeightedSupport.AllFullSupportProduct at hno
    push Not at hno
    obtain ⟨n,f,hf,hne,hnon⟩ := hno
    exact of_full_support_nonproduct (by omega) hX h0 h1 hBO f hf hne hnon

end
end Paper2.DegreeCSP.AllBOAffineResources
