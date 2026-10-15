import Paper2.DegreeCSP.BooleanGeneratedMaltsev
import Paper2.DegreeCSP.BooleanDiscriminatorAffine

/-! Actual original-table BO yields affine support indicators throughout the
literal degree-generated family. The common operation is proved from real
presentation conjunctions and cancellation-safe projections; it is not a
hypothesis of these endpoints. No coefficient classification is asserted. -/
namespace Paper2.DegreeCSP.BooleanGeneratedAffineSupport
open Tractable BooleanStructure BooleanGeneratedSupport
noncomputable section

/-- Literal X selects one of the two Boolean Mal'tsev operations. Both preserve
xor-closed supports, by the proved discriminator projection argument. -/
theorem generated_support_xor (F : SignatureFamily AlgebraicComplex) {k : ℕ}
    (hk : 0<k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hBO : OriginalBO.AllGeneratedOriginalBO F k) {n : ℕ}
    (f : Signature AlgebraicComplex n) (hf : Generated F k f) :
    Preserves xor3 {x | f x≠0} := by
  obtain ⟨m,hm,hpres⟩ := BooleanGeneratedMaltsev.common_support_operation F k hBO
  have hx : Preserves m disequalityRelation := by
    rw [← native_support]
    exact preserves_original F hk m hpres _ hX
  rcases maltsev_classification m hm hx with he | he
  · simpa only [he] using hpres n f hf
  · apply preserves_xor_of_discriminator
    simpa only [he] using hpres n f hf

/-- Every generated support has an actual finite affine-system indicator,
including the zero support and arity zero. -/
theorem generated_support_affine (F : SignatureFamily AlgebraicComplex) {k : ℕ}
    (hk : 0<k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hBO : OriginalBO.AllGeneratedOriginalBO F k) {n : ℕ}
    (f : Signature AlgebraicComplex n) (hf : Generated F k f) :
    Affine (indicator {x | f x≠0}) :=
  affine_indicator_of_xor _ (generated_support_xor F hk hX hBO f hf)

/-- Source members enter through their genuine k-copy presentations; positive
powers have exactly their original support. -/
theorem original_support_xor (F : SignatureFamily AlgebraicComplex) {k : ℕ}
    (hk : 0<k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (f : AnySignature AlgebraicComplex) (hf : f∈F) :
    Preserves xor3 {x | f.2 x≠0} := by
  have h := generated_support_xor F hk hX hBO (fun x=>f.2 x^k)
    (generated_power F f.2 hf (dvd_refl k))
  simpa only [power_support f.2 hk] using h

/-- The literal source support indicator is affine, while its coefficients
remain those of the supplied source signature. -/
theorem original_support_affine (F : SignatureFamily AlgebraicComplex) {k : ℕ}
    (hk : 0<k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (f : AnySignature AlgebraicComplex) (hf : f∈F) :
    Affine (indicator {x | f.2 x≠0}) :=
  affine_indicator_of_xor _ (original_support_xor F hk hX hBO f hf)

end
end Paper2.DegreeCSP.BooleanGeneratedAffineSupport
