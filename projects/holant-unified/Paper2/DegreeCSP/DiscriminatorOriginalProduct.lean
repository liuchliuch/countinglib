import Paper2.DegreeCSP.DiscriminatorSupportCoordinates
import Paper2.DegreeCSP.MultiCoordinatePadding
import Paper2.DegreeCSP.NoAnchorWeightedSupport
import Paper2.DegreeCSP.ProductCoordinateSubstitution
import Paper2.DegreeCSP.ClassesToTract

/-! The common discriminator case closes in the literal original product
class when all generated full-support tables are product. A signed coordinate
decoder is physically padded using the original source constraint once;
nonzero unary axis factors are then cancelled from that actual table. -/
namespace Paper2.DegreeCSP.DiscriminatorOriginalProduct
open scoped BigOperators
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem original_product {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hk : 2≤k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hno : NoAnchorWeightedSupport.AllFullSupportProduct F k)
    (f : Signature AlgebraicComplex n) (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F)
    (hd : BooleanStructure.Preserves BooleanStructure.discriminator {x|f x≠0}) :
    Product f := by
  classical
  by_cases hz:f=0
  · rw [hz]
    exact product_zero n
  have hex : ∃z,f z≠0 := by
    by_contra h
    apply hz
    funext z
    exact not_not.mp (not_exists.mp h z)
  obtain ⟨z,hz⟩:=hex
  obtain ⟨r,q,E,hq,live,selected,recover⟩:=
    DiscriminatorSupportCoordinates.exists_coordinates f z hz hd
  have ht : 0<k-1 := by omega
  have htk : k-1+1=k := by omega
  let g : Signature AlgebraicComplex r:=fun x=>f (MultiCoordinateContext.word E x)*
    ∏j,f (MultiCoordinateContext.word E (Function.update (fun _=>false) j (x j)))^(k-1)
  have hg : Generated F k g := by
    have h:=MultiCoordinateContext.padded_generated E F f hf h0 h1 hX ht
    rw [htk] at h
    exact h
  have hgne : ∀x,g x≠0 := by
    intro x
    exact mul_ne_zero (live x) (Finset.prod_ne_zero_iff.mpr
      (fun j _=>pow_ne_zero _ (live _)))
  have hp : Product (fun x=>f (MultiCoordinateContext.word E x)) :=
    MultiCoordinateContext.product_of_padded E f (k-1) live (hno r g hg hgne)
  have hind : Paper2.DegreeCSP.BooleanStructure.indicator {x|f x≠0}=
      (fun x=>if f x≠0 then (1 : AlgebraicComplex) else 0) := by
    funext x
    by_cases hx:f x≠0 <;> simp [Paper2.DegreeCSP.BooleanStructure.indicator,hx]
  have hs : Product (fun x=>if f x≠0 then (1 : AlgebraicComplex) else 0) := by
    rw [←hind]
    exact Paper2.DegreeCSP.BooleanStructure.product_indicator_of_discriminator _ hd
  exact ProductCoordinateSubstitution.reconstruct_live f
    (fun x=>f (MultiCoordinateContext.word E x)) hs hp q
    (fun x hx=>congrArg f (recover x hx))

theorem original_family_product (F : SignatureFamily AlgebraicComplex) {k : ℕ}
    (hk : 2≤k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hno : NoAnchorWeightedSupport.AllFullSupportProduct F k)
    (hd : ∀f∈F,BooleanStructure.Preserves BooleanStructure.discriminator {x|f.2 x≠0}) :
    ∀f∈F,Product f.2 :=
  fun f hf=>original_product hk hX h0 h1 hno f.2 hf (hd f hf)

/-- The complete discriminator/no-anchor branch returns the original source
tractability criterion, with the mandatory native edge witness installed. -/
theorem tract_family (F : SignatureFamily AlgebraicComplex) (hfin : F.Finite) {k : ℕ}
    (hk : 2≤k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hno : NoAnchorWeightedSupport.AllFullSupportProduct F k)
    (hd : ∀f∈F,BooleanStructure.Preserves BooleanStructure.discriminator {x|f.2 x≠0}) :
    Tract (familyAction sourceKBasis F) :=
  ClassesToTract.product_family F hfin (original_family_product F hk hX h0 h1 hno hd)

/-- The actual common operation on degree-generated tables transfers only
their support through k-copy presentations. Original coefficients are then
recovered by the one-copy physical padding proved above. -/
theorem tract_of_generated_discriminator (F : SignatureFamily AlgebraicComplex)
    (hfin : F.Finite) {k : ℕ} (hk : 2≤k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hno : NoAnchorWeightedSupport.AllFullSupportProduct F k)
    (hd : BooleanGeneratedSupport.CommonSupportOperation F k BooleanStructure.discriminator) :
    Tract (familyAction sourceKBasis F) :=
  tract_family F hfin hk hX h0 h1 hno
    (BooleanGeneratedSupport.preserves_original F (by omega) BooleanStructure.discriminator hd)

end
end Paper2.DegreeCSP.DiscriminatorOriginalProduct

