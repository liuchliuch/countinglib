import Paper2.DegreeCSP.DiscriminatorOriginalProduct
import Paper2.DegreeCSP.ProductSupport
import Paper2.DegreeCSP.NoAnchorParityGenerated
import Paper2.DegreeCSP.NoAnchorParityAffine

/-! The no-anchor branch retains the original source coefficients. Product
support indicators close through physical one-copy coordinate padding; a
genuine nonproduct support gives an actual weighted parity presentation,
which constrains every actually generated table to the affine class. -/
namespace Paper2.DegreeCSP.NoAnchorComplete
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem original_product_or_generated_affine (F : SignatureFamily AlgebraicComplex)
    {k : ℕ} (hk : 2≤k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (hno : NoAnchorWeightedSupport.AllFullSupportProduct F k) :
    (∀f∈F,Product f.2) ∨
      (∀(n : ℕ)(f : Signature AlgebraicComplex n),Generated F k f→Affine f) := by
  classical
  have hk0 : 0<k := by omega
  by_cases hs : ∀f∈F,Product (BooleanStructure.indicator {x|f.2 x≠0})
  · left
    apply DiscriminatorOriginalProduct.original_family_product F hk hX h0 h1 hno
    intro f hf
    exact ProductSupport.indicator_discriminator _ (hs f hf)
  obtain ⟨f,hf,hnon⟩ : ∃f∈F,¬Product (BooleanStructure.indicator {x|f.2 x≠0}) := by
    obtain ⟨f,hf⟩ := not_forall.mp hs
    obtain ⟨hmem,hnon⟩ := not_forall.mp hf
    exact ⟨f,hmem,hnon⟩
  have hex : ∃z,f.2 z≠0 := by
    by_contra none
    have he : BooleanStructure.indicator {x|f.2 x≠0}=0 := by
      funext x
      simp [BooleanStructure.indicator,not_exists.mp none x]
    exact hnon (he.symm ▸ product_zero f.1)
  obtain ⟨z,hz⟩:=hex
  let g : Signature AlgebraicComplex f.1:=fun x=>f.2 x^k
  have hg : Generated F k g:=generated_power F f.2 hf (dvd_refl k)
  have hgz : g z≠0:=pow_ne_zero k hz
  have hsupport : {x|g x≠0}={x|f.2 x≠0}:=BooleanGeneratedSupport.power_support f.2 hk0
  have hgnon : ¬Product (BooleanStructure.indicator {x|g x≠0}) := by
    rwa [hsupport]
  have hxor := BooleanGeneratedAffineSupport.generated_support_xor F hk0 hX hBO g hg
  have hp (b : Bool) : Generated F k (literalPin b) := by
    cases b
    · exact generated_literalPin hk0 false h0
    · exact generated_literalPin hk0 true h1
  obtain ⟨A,B,offset,hA,hB,hparity⟩:=NoAnchorParityGenerated.exists_weighted_parity
    hno hp g hg z hgz hxor hgnon
  right
  intro n f hf
  exact NoAnchorParityAffine.generated_affine hk0 hX hBO hno A B offset hA hB hparity
    (hp false) f hf

/-- If the unchanged source criterion excludes the product alternative,
every generated table is actually affine. The weighted parity resource and
all zero-support reconstruction are proved internally. -/
theorem generated_affine_of_not_tract (F : SignatureFamily AlgebraicComplex)
    (hfin : F.Finite) {k : ℕ} (hk : 2≤k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (hno : NoAnchorWeightedSupport.AllFullSupportProduct F k)
    (hnot : ¬Tract (familyAction sourceKBasis F)) :
    ∀(n : ℕ)(f : Signature AlgebraicComplex n),Generated F k f→Affine f := by
  rcases original_product_or_generated_affine F hk hX h0 h1 hBO hno with hp|ha
  · exact False.elim (hnot (ClassesToTract.product_family F hfin hp))
  · exact ha

end
end Paper2.DegreeCSP.NoAnchorComplete

