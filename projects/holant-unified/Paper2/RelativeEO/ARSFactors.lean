import Paper2.RelativeEO.ARSMatching

/-! Algebraic projective-ARS and EO inheritance by genuine tensor factors.
All factors already live in the original algebraic coefficient field; the
explicit scalar-descent theorem normalizes their phase without adjoining a
coordinate restriction or a complex-only representative as a gadget. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable

/-- A nonzero projective normalization gives one global phase identity. -/
theorem ProjectiveARS.phase {n : ℕ} {f : Signature AlgebraicComplex n}
    (h : ProjectiveARS f) :
    ∃ ρ : ℂ, ∀ x, (f x : ℂ) = ρ * star (f (fun i => !(x i)) : ℂ) := by
  obtain ⟨c,hc,h⟩ := h
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  refine ⟨(c : ℂ) / star (c : ℂ),?_⟩
  intro x
  have hh := h x
  simp only [star_mul,star_inv₀] at hh
  calc
    (f x : ℂ) = (c : ℂ) * ((c : ℂ)⁻¹ * (f x : ℂ)) := by
      rw [← mul_assoc,mul_inv_cancel₀ hcC,one_mul]
    _ = _ := by rw [hh]; ring

theorem ProjectiveARS.complement_nonzero {n : ℕ} {f : Signature AlgebraicComplex n}
    (h : ProjectiveARS f) (x : Fin n → Bool) (hx : f x ≠ 0) :
    f (fun i => !(x i)) ≠ 0 := by
  obtain ⟨ρ,hρ⟩ := h.phase
  intro hz
  have hh := hρ x
  rw [hz] at hh
  have hh' : (f x : ℂ) = 0 := by simpa using hh
  exact hx (Subtype.ext hh')

theorem ProjectiveARS.reindex {m n : ℕ} {f : Signature AlgebraicComplex m}
    (h : ProjectiveARS f) (e : Fin m ≃ Fin n) : ProjectiveARS (Tensor.reindex e f) := by
  obtain ⟨c,hc,h⟩ := h
  exact ⟨c,hc,fun x => h (fun i => x (e i))⟩

/-- Both ordered tensor factors inherit projective ARS over the algebraic field. -/
theorem tensor_factors_projectiveARS {m n : ℕ}
    (a : Signature AlgebraicComplex m) (b : Signature AlgebraicComplex n)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : ProjectiveARS (Signature.tensor a b)) :
    ProjectiveARS a ∧ ProjectiveARS b := by
  classical
  obtain ⟨x,hx⟩ : ∃ x, a x ≠ 0 := by by_contra h; push Not at h; exact ha (funext h)
  obtain ⟨y,hy⟩ : ∃ y, b y ≠ 0 := by by_contra h; push Not at h; exact hb (funext h)
  obtain ⟨ρ,hρ⟩ := h.phase
  have hxy (u : Fin m → Bool) (v : Fin n → Bool) :
      (a u : ℂ) * (b v : ℂ) =
        ρ * star (a (fun i => !(u i)) : ℂ) * star (b (fun i => !(v i)) : ℂ) := by
    have hh := hρ (Fin.append u v)
    simp only [Signature.tensor_apply,Fin.append_left,Fin.append_right] at hh
    change (a u : ℂ) * (b v : ℂ) = ρ * star
      ((a (fun i => !(u i)) : ℂ) * (b (fun i => !(v i)) : ℂ)) at hh
    simpa only [star_mul,mul_assoc,mul_comm,mul_left_comm] using hh
  have hxC : (a x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hyC : (b y : ℂ) ≠ 0 := by exact_mod_cast hy
  constructor
  · apply algebraic_ars_of_phase a ha (ρ * star (b (fun i => !(y i)) : ℂ) / (b y : ℂ))
    intro u
    have hh := hxy u y
    field_simp
    linear_combination hh
  · apply algebraic_ars_of_phase b hb (ρ * star (a (fun i => !(x i)) : ℂ) / (a x : ℂ))
    intro v
    have hh := hxy x v
    field_simp
    linear_combination hh

/-- The semantic EO support predicate agrees exactly with zero doubled charge. -/
theorem centralSupport_iff_chargeLayer {n : ℕ} (f : Signature AlgebraicComplex n) :
    Signature.CentralSupport f ↔ Tensor.ChargeLayer f 0 := by
  constructor
  · intro h x hx
    have hh : 2 * weight x = n := by by_contra hn; exact hx (h x hn)
    simp only [doubledCharge,Fintype.card_fin]
    omega
  · intro h x hx
    by_contra hn
    have hh := h x hn
    simp only [doubledCharge,Fintype.card_fin] at hh
    omega

theorem centralSupport_reindex {m n : ℕ} {f : Signature AlgebraicComplex m}
    (h : Signature.CentralSupport f) (e : Fin m ≃ Fin n) :
    Signature.CentralSupport (Tensor.reindex e f) :=
  (centralSupport_iff_chargeLayer _).mpr
    (Tensor.reindex_chargeLayer e ((centralSupport_iff_chargeLayer _).mp h))

/-- Doubled charge adds over the actual ordered tensor blocks. -/
theorem charge_append {m n : ℕ} (x : Fin m → Bool) (y : Fin n → Bool) :
    charge (Fin.append x y) = charge x + charge y := by
  have hw : weight (Fin.append x y) = weight x + weight y := by
    simp only [weight,Fin.sum_univ_add,Fin.append_left,Fin.append_right]
  simp only [charge,hw,Nat.cast_add]
  ring

/-- Complement symmetry excludes the one-sided tensor-factor exception to EO
inheritance: each factor itself has support only on its central layer. -/
theorem tensor_factors_central {m n : ℕ}
    (a : Signature AlgebraicComplex m) (b : Signature AlgebraicComplex n)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : Signature.CentralSupport (Signature.tensor a b))
    (hars : ProjectiveARS (Signature.tensor a b)) :
    Signature.CentralSupport a ∧ Signature.CentralSupport b := by
  classical
  obtain ⟨haARS,hbARS⟩ := tensor_factors_projectiveARS a b ha hb hars
  obtain ⟨x,hx⟩ : ∃ x, a x ≠ 0 := by by_contra h; push Not at h; exact ha (funext h)
  obtain ⟨y,hy⟩ : ∃ y, b y ≠ 0 := by by_contra h; push Not at h; exact hb (funext h)
  have hz (u : Fin m → Bool) (v : Fin n → Bool) (hu : a u ≠ 0) (hv : b v ≠ 0) :
      charge u + charge v = 0 := by
    have hn : Signature.tensor a b (Fin.append u v) ≠ 0 := by
      simpa only [Signature.tensor_apply,Fin.append_left,Fin.append_right] using mul_ne_zero hu hv
    have hh := ((centralSupport_iff_chargeLayer _).mp h) (Fin.append u v) hn
    have hh' : charge (Fin.append u v) = 0 := by
      simpa only [charge,doubledCharge,Fintype.card_fin] using hh
    simpa only [charge_append] using hh'
  constructor
  · intro u hu
    by_contra hne
    have h₁ := hz u y hne hy
    have h₂ := hz (fun i => !(u i)) y (haARS.complement_nonzero u hne) hy
    rw [charge_compl] at h₂
    unfold charge at h₁ h₂
    omega
  · intro v hv
    by_contra hne
    have h₁ := hz x v hx hne
    have h₂ := hz x (fun i => !(v i)) hx (hbARS.complement_nonzero v hne)
    rw [charge_compl] at h₂
    unfold charge at h₁ h₂
    omega

end Paper2.RelativeEO
