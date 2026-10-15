import Paper2.Tractable.Criteria

/-! Paper 2 Lemma 3.9's scalar-field correction. A complex projective ARS
witness for a nonzero algebraic table descends to an algebraic scalar, using
the actual coefficient ratio and the explicit alternatives 1+rho and i.
No EO hypothesis, complexity assumption, or literature lemma is used. -/
namespace Paper2.RelativeEO
open Paper2.Tractable

noncomputable def conjugateAlgebraic (z : AlgebraicComplex) : AlgebraicComplex :=
  ⟨star (z : ℂ), mem_algebraicClosure_iff.mpr (by
    simpa using IsAlgebraic.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom
      (mem_algebraicClosure_iff.mp z.property))⟩

@[simp] theorem coe_conjugateAlgebraic (z : AlgebraicComplex) :
    (conjugateAlgebraic z : ℂ) = star (z : ℂ) := rfl

/-- Explicit algebraic solution of c/conj(c)=rho for a norm-one phase. -/
theorem algebraic_phase_normalizer (ρ : AlgebraicComplex)
    (hρ : (ρ : ℂ) * star (ρ : ℂ) = 1) :
    ∃ c : AlgebraicComplex, c ≠ 0 ∧ (c : ℂ) / star (c : ℂ) = (ρ : ℂ) := by
  by_cases hneg : ρ = -1
  · refine ⟨imaginaryUnit, ?_, ?_⟩
    · intro hc
      exact Complex.I_ne_zero (congrArg Subtype.val hc)
    · rw [hneg]
      change Complex.I / star Complex.I = -1
      have hI : star Complex.I = -Complex.I := Complex.conj_I
      rw [hI]
      apply (div_eq_iff (neg_ne_zero.mpr Complex.I_ne_zero)).mpr
      ring
  · have hc : (1 : AlgebraicComplex) + ρ ≠ 0 := by
      intro hz
      apply hneg
      linear_combination hz
    have hcC : ((1 + ρ : AlgebraicComplex) : ℂ) ≠ 0 := by exact_mod_cast hc
    refine ⟨1 + ρ, hc, ?_⟩
    apply (div_eq_iff (star_ne_zero.mpr hcC)).mpr
    change 1 + (ρ : ℂ) = (ρ : ℂ) * star (1 + (ρ : ℂ))
    simp only [star_add, star_one]
    rw [mul_add, mul_one, hρ]
    ring

/-- A projective phase identity is normalized over the algebraic field.
The phase is recovered from one actual nonzero complementary coefficient pair. -/
theorem algebraic_ars_of_phase {n : ℕ} (f : Signature AlgebraicComplex n) (hf : f ≠ 0)
    (ρ : ℂ) (h : ∀ x, (f x : ℂ) = ρ * star (f (fun i => !(x i)) : ℂ)) :
    ∃ c : AlgebraicComplex, c ≠ 0 ∧
      ∀ x, (c : ℂ)⁻¹ * (f x : ℂ) = star ((c : ℂ)⁻¹ * (f (fun i => !(x i)) : ℂ)) := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hf (funext hn)
  have hxC : (f x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hb : star (f (fun i => !(x i)) : ℂ) ≠ 0 := by
    intro hz
    have hh := h x
    rw [hz, mul_zero] at hh
    exact hxC hh
  let r : AlgebraicComplex := f x / conjugateAlgebraic (f (fun i => !(x i)))
  have hr : (r : ℂ) = ρ := by
    change (f x : ℂ) / star (f (fun i => !(x i)) : ℂ) = ρ
    exact (div_eq_iff hb).mpr (h x)
  have hback := h (fun i => !(x i))
  simp only [Bool.not_not] at hback
  have hphase : ρ * star ρ = 1 := by
    apply mul_right_cancel₀ hxC
    calc
      (ρ * star ρ) * (f x : ℂ) = ρ * star (ρ * star (f x : ℂ)) := by
        simp only [star_mul, star_star]
        ring
      _ = ρ * star (f (fun i => !(x i)) : ℂ) := by rw [← hback]
      _ = (f x : ℂ) := (h x).symm
      _ = 1 * (f x : ℂ) := (one_mul _).symm
  obtain ⟨c, hc, hcr⟩ := algebraic_phase_normalizer r (by rw [hr]; exact hphase)
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hcbar : star (c : ℂ) ≠ 0 := star_ne_zero.mpr hcC
  refine ⟨c, hc, fun y => ?_⟩
  rw [hr] at hcr
  rw [h y, ← hcr, star_mul, star_inv₀]
  field_simp

/-- Exact source statement: any nonzero complex normalizing scalar for an
algebraic signature can be replaced by a nonzero algebraic normalizing scalar. -/
theorem algebraic_ars_of_complex_scalar {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : f ≠ 0) (c : ℂ) (hc : c ≠ 0)
    (h : ∀ x, c⁻¹ * (f x : ℂ) = star (c⁻¹ * (f (fun i => !(x i)) : ℂ))) :
    ∃ a : AlgebraicComplex, a ≠ 0 ∧
      ∀ x, (a : ℂ)⁻¹ * (f x : ℂ) = star ((a : ℂ)⁻¹ * (f (fun i => !(x i)) : ℂ)) := by
  apply algebraic_ars_of_phase f hf (c / star c)
  intro x
  calc
    (f x : ℂ) = c * (c⁻¹ * (f x : ℂ)) := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    _ = c * star (c⁻¹ * (f (fun i => !(x i)) : ℂ)) := by rw [h x]
    _ = (c / star c) * star (f (fun i => !(x i)) : ℂ) := by
      simp only [star_mul, star_inv₀, div_eq_mul_inv]
      ring

end Paper2.RelativeEO
