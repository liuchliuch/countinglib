import ComplexCSP.Algebra.ComplexRootCertificatesImages

/-! # Continuous real extensions of the finite rational certificate formulas -/

namespace ComplexCSP.ComplexRootCertificates

open Polynomial GaussianRational
open scoped BigOperators

noncomputable def complexTaylor {n : ℕ} (a : Code n) (c : ℂ) (j : ℕ) : ℂ :=
  ∑ i, (i.val.choose j : ℂ) * toComplex (a i) * c^(i.val-j)

noncomputable def complexUpper (z : ℂ) : ℝ := |z.re| + |z.im|
noncomputable def complexLower (z : ℂ) : ℝ := max |z.re| |z.im|

noncomputable def realDerivativeLower {n : ℕ} (a : Code n) (c : ℂ) : ℝ :=
  complexLower (complexTaylor a c 1)

noncomputable def realRemainderBound {n : ℕ} (a : Code n) (c : ℂ) (r : ℝ) : ℝ :=
  ∑ j : Fin n, ((j.val+2 : ℕ) : ℝ)*complexUpper (complexTaylor a c (j.val+2))*r^(j.val+1)

noncomputable def realImageRadius {n : ℕ} (a : Code n) (c : ℂ) (r : ℝ) : ℝ :=
  complexUpper (complexTaylor a c 1)*r +
    ∑ j : Fin n, complexUpper (complexTaylor a c (j.val+2))*r^(j.val+2)

@[simp] theorem complexTaylor_at_rational {n : ℕ} (a : Code n)
    (c : GaussianRational) (j : ℕ) :
    complexTaylor a (toComplex c) j = toComplex (taylorCoefficient a c j) := by
  simp [complexTaylor, taylorCoefficient]

@[simp] theorem complexUpper_at_rational (z : GaussianRational) :
    complexUpper (toComplex z) = (upper z : ℝ) := by simp [complexUpper, upper]

@[simp] theorem complexLower_at_rational (z : GaussianRational) :
    complexLower (toComplex z) = (lower z : ℝ) := by simp [complexLower, lower]

@[simp] theorem realDerivativeLower_at_rational {n : ℕ} (a : Code n) (c : GaussianRational) :
    realDerivativeLower a (toComplex c) = (derivativeLower a c : ℝ) := by
  simp [realDerivativeLower, derivativeLower]

@[simp] theorem realRemainderBound_at_rational {n : ℕ} (a : Code n)
    (c : GaussianRational) (r : ℚ) :
    realRemainderBound a (toComplex c) (r:ℝ) = (remainderBound a c r : ℝ) := by
  simp [realRemainderBound, remainderBound]

@[simp] theorem realImageRadius_at_rational {n : ℕ} (a : Code n)
    (c : GaussianRational) (r : ℚ) :
    realImageRadius a (toComplex c) (r:ℝ) = (imageRadius a c r : ℝ) := by
  simp [realImageRadius, imageRadius]

theorem complexTaylor_eq {n : ℕ} (a : Code n) (c : ℂ) (j : ℕ) :
    complexTaylor a c j = ((Polynomial.taylor c) (denote a)).coeff j := by
  rw [Polynomial.taylor_coeff]
  simp [complexTaylor, denote, Polynomial.hasseDeriv_monomial, Polynomial.eval_finset_sum]

@[simp] theorem complexTaylor_zero {n : ℕ} (a : Code n) (c : ℂ) :
    complexTaylor a c 0 = (denote a).eval c := by rw [complexTaylor_eq, Polynomial.taylor_coeff_zero]

@[simp] theorem complexTaylor_one {n : ℕ} (a : Code n) (c : ℂ) :
    complexTaylor a c 1 = (denote a).derivative.eval c := by
  rw [complexTaylor_eq, Polynomial.taylor_coeff_one]

theorem complexLower_pos {z : ℂ} (hz : z ≠ 0) : 0 < complexLower z := by
  by_contra h
  have hmax : max |z.re| |z.im| ≤ 0 := le_of_not_gt h
  have hreal : z.re = 0 := abs_eq_zero.mp (le_antisymm ((le_max_left _ _).trans hmax) (abs_nonneg _))
  have himag : z.im = 0 := abs_eq_zero.mp (le_antisymm ((le_max_right _ _).trans hmax) (abs_nonneg _))
  exact hz (Complex.ext hreal himag)

@[continuity, fun_prop] theorem continuous_complexTaylor {n : ℕ} (a : Code n) (j : ℕ) :
    Continuous (fun c : ℂ ↦ complexTaylor a c j) := by
  unfold complexTaylor
  fun_prop

@[continuity, fun_prop] theorem continuous_complexUpper : Continuous complexUpper := by
  unfold complexUpper
  fun_prop

@[continuity, fun_prop] theorem continuous_complexLower : Continuous complexLower := by
  unfold complexLower
  fun_prop

@[continuity, fun_prop] theorem continuous_realDerivativeLower {n : ℕ} (a : Code n) :
    Continuous (realDerivativeLower a) := by
  unfold realDerivativeLower
  fun_prop

@[continuity, fun_prop] theorem continuous_realRemainderBound {n : ℕ} (a : Code n) :
    Continuous (fun p : ℂ × ℝ ↦ realRemainderBound a p.1 p.2) := by
  unfold realRemainderBound
  fun_prop

@[continuity, fun_prop] theorem continuous_realImageRadius {n : ℕ} (a : Code n) :
    Continuous (fun p : ℂ × ℝ ↦ realImageRadius a p.1 p.2) := by
  unfold realImageRadius
  fun_prop

@[simp] theorem realRemainderBound_zero {n : ℕ} (a : Code n) (c : ℂ) :
    realRemainderBound a c 0 = 0 := by simp [realRemainderBound]

@[simp] theorem realImageRadius_zero {n : ℕ} (a : Code n) (c : ℂ) :
    realImageRadius a c 0 = 0 := by simp [realImageRadius]

/-- The strict inequalities whose rational specialization is the executable
root certificate, leaving the separately chosen radius-positivity condition out. -/
def RealRootGood {n : ℕ} (a : Code n) (c : ℂ) (r : ℝ) : Prop :=
  0 < realDerivativeLower a c ∧
  realRemainderBound a c r < realDerivativeLower a c ∧
  complexUpper (complexTaylor a c 0) + realRemainderBound a c r*r < realDerivativeLower a c*r

def RealImageGood {n : ℕ} (a : Code n) (c : ℂ) (r : ℝ) (box : Rectangle) : Prop :=
  (box.reLo : ℝ) < (complexTaylor a c 0).re-realImageRadius a c r ∧
  (complexTaylor a c 0).re+realImageRadius a c r < (box.reHi : ℝ) ∧
  (box.imLo : ℝ) < (complexTaylor a c 0).im-realImageRadius a c r ∧
  (complexTaylor a c 0).im+realImageRadius a c r < (box.imHi : ℝ)

theorem realRootGood_rational_iff {n : ℕ} (a : Code n) (c : GaussianRational)
    (r : ℚ) (hr : 0 < r) : RealRootGood a (toComplex c) (r:ℝ) ↔
      rootCertificate a c r = true := by
  simp only [RealRootGood, rootCertificate, decide_eq_true_eq, hr, true_and,
    realDerivativeLower_at_rational, realRemainderBound_at_rational,
    complexTaylor_at_rational, complexUpper_at_rational]
  norm_cast

theorem realImageGood_rational_iff {n : ℕ} (a : Code n) (c : GaussianRational)
    (r : ℚ) (hr : 0 ≤ r) (box : Rectangle) : RealImageGood a (toComplex c) (r:ℝ) box ↔
      imageCertificate a c r box = true := by
  simp only [RealImageGood, imageCertificate, decide_eq_true_eq, hr, true_and,
    realImageRadius_at_rational, complexTaylor_at_rational, toComplex_re, toComplex_im]
  norm_cast

end ComplexCSP.ComplexRootCertificates
