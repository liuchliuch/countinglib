import Paper2.DegreeCSP.NoAnchorComplete
import Paper2.DegreeCSP.GeneratedCodeSeven

/-! In the no-anchor branch, failure of the original product class supplies
an actual scaled seven-character code mask. A nonproduct original support
enters through its genuine k-copy presentation; its unique-fiber parity
minor and the affine fourth-power construction retain every scalar. -/
namespace Paper2.DegreeCSP.NoAnchorGeneratedCodeMask
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The code mask is produced internally from actual source membership and
degree-generated BO. No parity or mask resource is assumed. -/
theorem exists_scaled_code (F : SignatureFamily AlgebraicComplex) {k : ℕ}
    (hk : 2≤k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (hno : NoAnchorWeightedSupport.AllFullSupportProduct F k)
    (hnot : ¬(∀f∈F,Product f.2)) :
    ∃c : AlgebraicComplex,c≠0 ∧
      Generated F k (fun x : Fin 7→Bool=>c*GeneratedCodeSeven.indicator x) := by
  classical
  have hk0 : 0<k := by omega
  have hnon : ¬(∀f∈F,Product (BooleanStructure.indicator {x|f.2 x≠0})) := by
    intro hs
    apply hnot
    apply DiscriminatorOriginalProduct.original_family_product F hk hX h0 h1 hno
    intro f hf
    exact ProductSupport.indicator_discriminator _ (hs f hf)
  obtain ⟨f,hf,hs⟩ : ∃f∈F,¬Product (BooleanStructure.indicator {x|f.2 x≠0}) := by
    obtain ⟨f,hf⟩ := not_forall.mp hnon
    obtain ⟨hmem,hs⟩ := not_forall.mp hf
    exact ⟨f,hmem,hs⟩
  have hex : ∃z,f.2 z≠0 := by
    by_contra none
    have he : BooleanStructure.indicator {x|f.2 x≠0}=0 := by
      funext x
      simp [BooleanStructure.indicator,not_exists.mp none x]
    exact hs (he.symm ▸ product_zero f.1)
  obtain ⟨z,hz⟩ := hex
  let g : Signature AlgebraicComplex f.1 := fun x=>f.2 x^k
  have hg : Generated F k g := generated_power F f.2 hf (dvd_refl k)
  have hgz : g z≠0 := pow_ne_zero k hz
  have hsupport : {x|g x≠0}={x|f.2 x≠0} :=
    BooleanGeneratedSupport.power_support f.2 hk0
  have hgnon : ¬Product (BooleanStructure.indicator {x|g x≠0}) := by
    rwa [hsupport]
  have hxor := BooleanGeneratedAffineSupport.generated_support_xor F hk0 hX hBO g hg
  have hp (b : Bool) : Generated F k (literalPin b) := by
    cases b
    · exact generated_literalPin hk0 false h0
    · exact generated_literalPin hk0 true h1
  obtain ⟨A,B,offset,hA,hB,hparity⟩ :=
    NoAnchorParityGenerated.exists_weighted_parity hno hp g hg z hgz hxor hgnon
  have ha : Affine (NoAnchorWeightedParity.table A B offset) :=
    NoAnchorParityAffine.generated_affine hk0 hX hBO hno A B offset hA hB hparity
      (hp false) _ hparity
  exact GeneratedCodeSeven.exists_scaled_code hk0 hX A B offset hA hB hparity ha

end
end Paper2.DegreeCSP.NoAnchorGeneratedCodeMask

