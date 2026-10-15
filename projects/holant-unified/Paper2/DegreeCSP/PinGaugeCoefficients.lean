import Paper2.DegreeCSP.AxisRatioSigns

/-! Exact cancellation of the separable weights produced by literal pin
padding. The coefficient equations are retained, including their phases. -/
namespace Paper2.DegreeCSP.PinGaugeCoefficients
open scoped BigOperators
open AxisRatioSigns
noncomputable section
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

def weight (f : (ι → Bool) → K) (t : ℕ) (x : ι → Bool) : K :=
  ∏ j, f (Function.update zeroWord j (x j)) ^ t

def padded (f : (ι → Bool) → K) (t : ℕ) (x : ι → Bool) : K :=
  f x * weight f t x

theorem weight_nonzero (f : (ι → Bool) → K) (hf : ∀ x,f x ≠ 0)
    (t : ℕ) (x : ι → Bool) : weight f t x ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _j _ => pow_ne_zero t (hf _))

theorem padded_nonzero (f : (ι → Bool) → K) (hf : ∀ x,f x ≠ 0)
    (t : ℕ) (x : ι → Bool) : padded f t x ≠ 0 :=
  mul_ne_zero (hf _) (weight_nonzero f hf t x)

/-- Separable pin weights have the same product on opposite corners. -/
theorem weight_rectangle (f : (ι → Bool) → K) (t : ℕ) (i : ι)
    (x : ι → Bool) (hx : x i = false) :
    weight f t x * weight f t (Function.update zeroWord i true) =
      weight f t (Function.update x i true) * weight f t zeroWord := by
  simp only [weight,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : j = i
  · subst j
    simp [hx,zeroWord,mul_comm]
  · simp [Function.update,h,zeroWord]

/-- An actual squared cross equation for the padded table yields the precise
coordinate-edge ratio of the original coefficients. -/
theorem edge_square (f : (ι → Bool) → K) (hf : ∀ x,f x ≠ 0)
    (t : ℕ) (i : ι) (x : ι → Bool) (hx : x i = false)
    (he : (padded f t x * padded f t (Function.update zeroWord i true)) ^ 2 =
      (padded f t (Function.update x i true) * padded f t zeroWord) ^ 2) :
    f (Function.update x i true) ^ 2 = axisRatio f i ^ 2 * f x ^ 2 := by
  have hw := weight_rectangle f t i x hx
  have hh : (f x * f (Function.update zeroWord i true)) ^ 2 =
      (f (Function.update x i true) * f zeroWord) ^ 2 := by
    apply mul_right_cancel₀ (pow_ne_zero 2 (mul_ne_zero (weight_nonzero f hf t x)
      (weight_nonzero f hf t (Function.update zeroWord i true))))
    calc
      _ = (padded f t x * padded f t (Function.update zeroWord i true)) ^ 2 := by
        dsimp [padded]
        ring
      _ = (padded f t (Function.update x i true) * padded f t zeroWord) ^ 2 := he
      _ = _ := by
        dsimp [padded]
        rw [show f (Function.update x i true) * weight f t (Function.update x i true) *
          (f zeroWord * weight f t zeroWord) =
          (f (Function.update x i true) * f zeroWord) *
          (weight f t (Function.update x i true) * weight f t zeroWord) by ring,← hw]
        ring
  rw [axisRatio,div_pow]
  field_simp [hf zeroWord]
  linear_combination -hh

/-- The full-support normal form follows from the displayed padded equations;
the sign remains an explicit Boolean function, not an assumed quadratic. -/
theorem signs (f : (ι → Bool) → K) (hf : ∀ x,f x ≠ 0) (t : ℕ)
    (he : ∀ i x,x i = false →
      (padded f t x * padded f t (Function.update zeroWord i true)) ^ 2 =
        (padded f t (Function.update x i true) * padded f t zeroWord) ^ 2) :
    (∀ i,axisRatio f i ≠ 0) ∧
      ∃ P : (ι → Bool) → Bool,P zeroWord = false ∧ ∀ x,
        f x = f zeroWord * (∏ i,if x i then axisRatio f i else 1) *
          (if P x then -1 else 1) :=
  signs_of_squared_edge_ratios f hf (fun i x hx => edge_square f hf t i x hx (he i x hx))

end
end Paper2.DegreeCSP.PinGaugeCoefficients
