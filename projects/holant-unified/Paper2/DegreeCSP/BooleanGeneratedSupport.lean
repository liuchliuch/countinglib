import Paper2.DegreeCSP.Generated

/-! The Boolean specialization consumes one operation on the literal degree-
generated partial-table family. Original supports are transferred through their
actual k-copy presentations. Coefficients are retained by Generated; the result
below classifies support indicators only. -/
namespace Paper2.DegreeCSP
noncomputable section
namespace BooleanGeneratedSupport
open BooleanStructure Tractable

def CommonSupportOperation (F : SignatureFamily AlgebraicComplex) (k : ℕ)
    (m : Operation) : Prop :=
  ∀ (n : ℕ) (f : Signature AlgebraicComplex n), Generated F k f →
    Preserves m {x | f x ≠ 0}

theorem power_support {n : ℕ} (f : Signature AlgebraicComplex n) {k : ℕ}
    (hk : 0 < k) : {x | f x ^ k ≠ 0} = {x | f x ≠ 0} := by
  ext x
  by_cases h : f x = 0
  · simp [h,Nat.ne_of_gt hk]
  · simp [h]

/-- A generator is used exactly k times, so this transfer respects degrees at
each ordered port, including arity zero. -/
theorem preserves_original (F : SignatureFamily AlgebraicComplex) {k : ℕ}
    (hk : 0 < k) (m : Operation) (h : CommonSupportOperation F k m)
    (f : AnySignature AlgebraicComplex) (hf : f ∈ F) :
    Preserves m {x | f.2 x ≠ 0} := by
  have hp := h f.1 (fun x => f.2 x ^ k)
    (generated_power F f.2 hf (dvd_refl k))
  simpa only [power_support f.2 hk] using hp

theorem native_support :
    {x | kernelSignature (Signature.disequality (K := AlgebraicComplex)) x ≠ 0} =
      disequalityRelation := by
  ext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [kernelSignature,Signature.disequality,disequalityRelation,h0,h1]

/-- One common operation yields one common support alternative for the whole
language. The conclusion does not identify original coefficients with their
indicators. -/
theorem support_classes (F : SignatureFamily AlgebraicComplex) {k : ℕ}
    (hk : 0 < k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F)
    (m : Operation) (hm : IsMaltsev m) (h : CommonSupportOperation F k m) :
    (∀ f ∈ F, Tractable.Affine (indicator {x | f.2 x ≠ 0})) ∨
      (∀ f ∈ F, Tractable.Product (indicator {x | f.2 x ≠ 0})) := by
  have hx : Preserves m disequalityRelation := by
    rw [← native_support]
    exact preserves_original F hk m h _ hX
  rcases maltsev_classification m hm hx with he | he
  · left
    intro f hf
    apply affine_indicator_of_xor
    simpa only [he] using preserves_original F hk m h f hf
  · right
    intro f hf
    apply product_indicator_of_discriminator
    simpa only [he] using preserves_original F hk m h f hf

end BooleanGeneratedSupport
end
end Paper2.DegreeCSP
