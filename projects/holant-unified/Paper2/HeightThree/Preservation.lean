import Paper2.Mountain
import Paper2.Paper1Accepted
import Paper2.Tractable.Downward

/-! The source hypotheses retained when adjoining the actual EO output of the
height-three construction. These statements preserve the literal language;
no relative-EO classification is postulated here. -/
namespace Paper2.HeightThree
open Tractable ExactInput

/-- Central support implies every supported half-charge is literally zero. -/
theorem eo_halfCharge_zero (f : AnySignature AlgebraicComplex) (hf : IsEO f)
    (x : Fin f.1 → Bool) (hx : f.2 x ≠ 0) : halfCharge x = 0 := by
  have hw : 2 * weight x = f.1 := by
    by_contra hn
    exact hx (hf.2 x hn)
  simp only [halfCharge, Fintype.card_fin]
  omega

theorem eo_halfCharge_divisible (f : AnySignature AlgebraicComplex) (hf : IsEO f)
    (d : ℤ) : Tensor.HalfChargeDivisible f.2 d := by
  intro x hx
  rw [eo_halfCharge_zero f hf x hx]
  exact dvd_zero d

/-- A mountain is a literal obstruction to both shared one-sided orientations. -/
theorem mountain_not_commonOneSided (F : SignatureFamily AlgebraicComplex)
    {d : ℕ} (M : Signature AlgebraicComplex (2*d)) (hM : IsMountain M)
    (hmem : (⟨2*d,M⟩ : AnySignature AlgebraicComplex) ∈ F) : ¬ CommonOneSided F := by
  intro hs
  have hd := hM.height_pos
  rcases hs with hs | hs
  · have h := hs _ hmem (fun _ => false) hM.zero_ne_zero
    simp only [charge, weight_false, Nat.cast_zero, mul_zero, zero_sub] at h
    omega
  · have h := hs _ hmem (fun _ => true) hM.one_ne_zero
    simp only [charge, weight_true, Fintype.card_fin] at h
    omega

/-- The EO table contributes charge zero, so every original divisibility
constraint survives exactly, for any positive or zero divisor. -/
theorem insert_eo_halfCharge_divisible (F : SignatureFamily AlgebraicComplex)
    (h : AnySignature AlgebraicComplex) (he : IsEO h) (d : ℤ)
    (hF : ∀ f ∈ F, Tensor.HalfChargeDivisible f.2 d) :
    ∀ f ∈ insert h F, Tensor.HalfChargeDivisible f.2 d := by
  intro f hf
  rcases hf with rfl | hf
  · exact eo_halfCharge_divisible f he d
  · exact hF f hf

theorem insert_eo_even (F : SignatureFamily AlgebraicComplex)
    (h : AnySignature AlgebraicComplex) (he : IsEO h)
    (hF : ∀ f ∈ F, Even f.1) : ∀ f ∈ insert h F, Even f.1 := by
  intro f hf
  rcases hf with rfl | hf
  · obtain ⟨d, hd⟩ := he.1
    rw [hd]
    exact even_two_mul d
  · exact hF f hf

/-- Preprocessing is retained without deleting any original language member. -/
theorem insert_nonzero_positive_preprocessed (F : SignatureFamily AlgebraicComplex)
    (h : AnySignature AlgebraicComplex) (hn : 0 < h.1) (hz : h.2 ≠ 0)
    (hF : Preprocessed F) : Preprocessed (insert h F) := by
  intro f hf
  rcases hf with rfl | hf
  · exact ⟨hn, hz⟩
  · exact hF f hf

/-- Nontractability travels upward while the same normalized K is retained. -/
theorem retained_nontractable (L A : Language) (hLA : L.family ⊆ A.family)
    (hnot : ¬ Tract (kImage L)) : ¬ Tract (kImage A) :=
  fun h => hnot (h.mono_family (familyAction_mono sourceKBasis hLA))

end Paper2.HeightThree
