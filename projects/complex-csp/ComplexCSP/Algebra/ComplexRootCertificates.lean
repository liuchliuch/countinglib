import ComplexCSP.Algebra.ComplexRootCertificatesBounds
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Executable rational complex-root certificates

All runtime data are Gaussian rational coefficient vectors, a Gaussian rational
center, and a positive rational radius. Native polynomials occur only in the
semantic proof layer. The checker uses strict rational inequalities.
-/

namespace ComplexCSP.ComplexRootCertificates

open Polynomial GaussianRational
open scoped BigOperators

/-- At least two coefficient slots, with arbitrary trailing zero padding. -/
abbrev Code (n : ℕ) := Fin (n+2) → GaussianRational

noncomputable def denote {n : ℕ} (a : Code n) : Polynomial ℂ :=
  ∑ i, Polynomial.monomial i.val (toComplex (a i))

/-- Direct finite Taylor coefficient computation, using only exact arithmetic. -/
def taylorCoefficient {n : ℕ} (a : Code n) (c : GaussianRational) (j : ℕ) :
    GaussianRational :=
  ∑ i, (i.val.choose j : GaussianRational) * a i * c^(i.val-j)

def derivativeLower {n : ℕ} (a : Code n) (c : GaussianRational) : ℚ :=
  lower (taylorCoefficient a c 1)

def remainderBound {n : ℕ} (a : Code n) (c : GaussianRational) (r : ℚ) : ℚ :=
  ∑ j : Fin n, ((j.val+2 : ℕ) : ℚ) *
    upper (taylorCoefficient a c (j.val+2)) * r^(j.val+1)

def rootCertificate {n : ℕ} (a : Code n) (c : GaussianRational) (r : ℚ) : Bool :=
  let L := derivativeLower a c
  let B := remainderBound a c r
  decide (0 < r ∧ 0 < L ∧ B < L ∧
    upper (taylorCoefficient a c 0) + B*r < L*r)

theorem taylorCoefficient_correct {n : ℕ} (a : Code n) (c : GaussianRational) (j : ℕ) :
    toComplex (taylorCoefficient a c j) =
      ((Polynomial.taylor (toComplex c)) (denote a)).coeff j := by
  rw [Polynomial.taylor_coeff]
  simp [taylorCoefficient, denote, Polynomial.hasseDeriv_monomial, Polynomial.eval_finset_sum]

theorem denote_degree_bound {n : ℕ} (a : Code n) : (denote a).natDegree < n+2 := by
  apply Nat.lt_succ_of_le
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp only [denote, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg]
  have := i.isLt
  omega

/-- Exact Taylor expansion into its constant, linear, and finite remainder. -/
theorem eval_eq_taylor {n : ℕ} (a : Code n) (c : GaussianRational) (z : ℂ) :
    (denote a).eval (z + toComplex c) =
      toComplex (taylorCoefficient a c 0) +
      toComplex (taylorCoefficient a c 1)*z +
      tailEval (fun j : Fin n ↦ toComplex (taylorCoefficient a c (j.val+2))) z := by
  rw [← Polynomial.taylor_eval]
  rw [Polynomial.eval_eq_sum_range' (by
    rw [Polynomial.natDegree_taylor]
    exact denote_degree_bound a), Finset.sum_range]
  simp_rw [← taylorCoefficient_correct]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, zero_add, pow_one]
  simp only [tailEval, add_assoc]

theorem remainderBound_correct {n : ℕ} (a : Code n) (c : GaussianRational)
    (r : ℚ) (hr : 0 ≤ r) :
    tailBound (fun j : Fin n ↦ toComplex (taylorCoefficient a c (j.val+2))) (r:ℝ) ≤
      (remainderBound a c r : ℝ) := by
  simp only [tailBound, remainderBound, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_pow]
  apply Finset.sum_le_sum
  intro j _
  gcongr
  exact norm_le_upper _

/-- Acceptance certifies exactly one root in the closed complex disk. -/
theorem rootCertificate_sound {n : ℕ} (a : Code n) (c : GaussianRational)
    (r : ℚ) (h : rootCertificate a c r = true) :
    ∃! z : ℂ, ‖z-toComplex c‖ ≤ (r:ℝ) ∧ (denote a).eval z = 0 := by
  simp only [rootCertificate, decide_eq_true_eq] at h
  obtain ⟨hr,hL,hBL,hsmall⟩ := h
  let t₀ := toComplex (taylorCoefficient a c 0)
  let t₁ := toComplex (taylorCoefficient a c 1)
  let tail := fun j : Fin n ↦ toComplex (taylorCoefficient a c (j.val+2))
  have hsmall' : ‖t₀‖ + (remainderBound a c r : ℝ)*(r:ℝ) <
      (derivativeLower a c : ℝ)*(r:ℝ) := by
    calc
      ‖t₀‖ + (remainderBound a c r : ℝ)*(r:ℝ) ≤
          (upper (taylorCoefficient a c 0) : ℝ) + (remainderBound a c r : ℝ)*(r:ℝ) :=
        add_le_add (norm_le_upper (taylorCoefficient a c 0)) le_rfl
      _ < _ := by exact_mod_cast hsmall
  obtain ⟨u,hu,hunique⟩ := unique_root_of_bounds t₀ t₁ tail (r:ℝ)
    (derivativeLower a c : ℝ) (remainderBound a c r : ℝ)
    (by exact_mod_cast hr) (by exact_mod_cast hL) (lower_le_norm _)
    (remainderBound_correct a c r hr.le) (by exact_mod_cast hBL) hsmall'
  refine ⟨u + toComplex c, ⟨by simpa using hu.1, ?_⟩, ?_⟩
  · rw [eval_eq_taylor]
    exact hu.2
  · intro z hz
    have he : t₀ + t₁*(z-toComplex c) + tailEval tail (z-toComplex c) = 0 := by
      rw [← eval_eq_taylor a c, sub_add_cancel]
      exact hz.2
    have heq := hunique (z-toComplex c) ⟨hz.1,he⟩
    linear_combination heq

end ComplexCSP.ComplexRootCertificates
