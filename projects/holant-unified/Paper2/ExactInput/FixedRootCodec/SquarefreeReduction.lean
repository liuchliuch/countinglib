import Paper2.ExactInput.FixedRootCodec.EuclideanGCD
import Paper2.ExactInput.FixedRootCodec.EuclideanQuotient
import Mathlib.RingTheory.Polynomial.Radical
import Mathlib.FieldTheory.Perfect

/-! Actual squarefree reduction of runtime rational coefficient vectors.
The Euclidean GCD retains its scalar unit, and the actual quotient circuit
divides by this computed polynomial. Its squarefreeness and preservation of
real and complex roots follow from the proved GCD divisor property. -/
namespace Paper2.ExactInput.FixedRootCodec.VariablePolynomial
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines Polynomial
open EuclideanDomain UniqueFactorizationMonoid
noncomputable section

theorem gcd_dvd_polynomial {p g : ℚ[X]}
    (hg : ∀ a : ℚ[X], a ∣ g ↔ a ∣ p ∧ a ∣ p.derivative) : g ∣ p :=
  ((hg g).mp dvd_rfl).1

theorem gcd_dvd_derivative {p g : ℚ[X]}
    (hg : ∀ a : ℚ[X], a ∣ g ↔ a ∣ p ∧ a ∣ p.derivative) : g ∣ p.derivative :=
  ((hg g).mp dvd_rfl).2

theorem quotient_ne_zero_of_gcd {p g : ℚ[X]} (hp : p ≠ 0) (hg0 : g ≠ 0)
    (hg : ∀ a : ℚ[X], a ∣ g ↔ a ∣ p ∧ a ∣ p.derivative) : p / g ≠ 0 := by
  have hi := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_polynomial hg)
  intro hz
  rw [hz,mul_zero] at hi
  exact hp hi.symm

theorem quotient_dvd_radical_of_gcd {p g : ℚ[X]} (hp : p ≠ 0) (hg0 : g ≠ 0)
    (hg : ∀ a : ℚ[X], a ∣ g ↔ a ∣ p ∧ a ∣ p.derivative) : p / g ∣ radical p := by
  have hd : divRadical p ∣ g := (hg _).mpr
    ⟨divRadical_dvd_self p,divRadical_dvd_derivative p⟩
  obtain ⟨t,ht⟩ := hd
  have hi := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_polynomial hg)
  have he : divRadical p * (t * (p/g)) = divRadical p * radical p := by
    calc
      _ = g * (p/g) := by rw [ht]; ring
      _ = p := hi
      _ = divRadical p * radical p := divRadical_mul_radical.symm
  have hc := mul_left_cancel₀ (divRadical_ne_zero hp) he
  exact ⟨t,by simpa [mul_comm] using hc.symm⟩

theorem quotient_squarefree_of_gcd {p g : ℚ[X]} (hp : p ≠ 0) (hg0 : g ≠ 0)
    (hg : ∀ a : ℚ[X], a ∣ g ↔ a ∣ p ∧ a ∣ p.derivative) : Squarefree (p / g) :=
  Squarefree.squarefree_of_dvd (quotient_dvd_radical_of_gcd hp hg0 hg) squarefree_radical

theorem quotient_separable_of_gcd {p g : ℚ[X]} (hp : p ≠ 0) (hg0 : g ≠ 0)
    (hg : ∀ a : ℚ[X], a ∣ g ↔ a ∣ p ∧ a ∣ p.derivative) : (p / g).Separable :=
  PerfectField.separable_iff_squarefree.mpr (quotient_squarefree_of_gcd hp hg0 hg)

theorem quotient_natDegree_le_of_gcd {p g : ℚ[X]} (hp : p ≠ 0)
    (hg : ∀ a : ℚ[X], a ∣ g ↔ a ∣ p ∧ a ∣ p.derivative) :
    (p / g).natDegree ≤ p.natDegree :=
  natDegree_le_of_dvd (div_dvd_of_dvd (gcd_dvd_polynomial hg)) hp

theorem polynomial_dvd_derivative_mul_quotient {p g : ℚ[X]} (hg0 : g ≠ 0)
    (hg : ∀ a : ℚ[X], a ∣ g ↔ a ∣ p ∧ a ∣ p.derivative) :
    p ∣ p.derivative * (p / g) := by
  have hi := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_polynomial hg)
  obtain ⟨t,ht⟩ := gcd_dvd_derivative hg
  refine ⟨t,?_⟩
  calc
    p.derivative * (p/g) = (g * (p/g)) * t := by rw [ht]; ring
    _ = p * t := by rw [hi]

theorem quotient_eval₂_zero_iff_of_gcd {K : Type*} [Field K] [CharZero K]
    {p g : ℚ[X]} (hp : p ≠ 0) (hg0 : g ≠ 0)
    (hg : ∀ a : ℚ[X], a ∣ g ↔ a ∣ p ∧ a ∣ p.derivative)
    (φ : ℚ →+* K) (z : K) : (p/g).eval₂ φ z = 0 ↔ p.eval₂ φ z = 0 := by
  have hmap : p.map φ ≠ 0 := (Polynomial.map_ne_zero_iff φ.injective).mpr hp
  have hdiv : p.map φ ∣ (p.map φ).derivative * (p/g).map φ := by
    simpa only [Polynomial.map_mul,derivative_map] using
      Polynomial.map_dvd φ (polynomial_dvd_derivative_mul_quotient hg0 hg)
  constructor
  · exact Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero φ z
      (div_dvd_of_dvd (gcd_dvd_polynomial hg))
  · intro hz
    have hr : (p.map φ).IsRoot z := by simpa only [IsRoot,eval_map] using hz
    have hq := isRoot_of_isRoot_of_dvd_derivative_mul hmap hdiv hr
    simpa only [IsRoot,eval_map] using hq

def squarefreeVector {n : ℕ} (v : Fin n → ℚ) : Fin n → ℚ :=
  quotient (v,gcdVector (v,derivative v))

def squarefreeComputes (n : ℕ) :
    Computes (vectorEncoding n) (vectorEncoding n) (squarefreeVector (n := n)) :=
  congrComputes ((pairComputes (identityComputes (vectorEncoding n))
    (derivativeGCDComputes n)).andThen (quotientComputes n)) (fun _ => rfl)

theorem squarefreeVector_polynomial {n : ℕ} (v : Fin n → ℚ) :
    polynomial (squarefreeVector v) = polynomial v / polynomial (gcdVector (v,derivative v)) :=
  quotient_polynomial _

theorem derivativeGCD_polynomial_ne_zero {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0) :
    polynomial (gcdVector (v,derivative v)) ≠ 0 := by
  exact (polynomial_eq_zero_iff _).not.mpr (gcdVector_ne_zero _ (Or.inl hv))

theorem squarefreeVector_ne_zero {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0) :
    squarefreeVector v ≠ 0 := by
  apply (polynomial_eq_zero_iff _).not.mp
  rw [squarefreeVector_polynomial]
  exact quotient_ne_zero_of_gcd ((polynomial_eq_zero_iff v).not.mpr hv)
    (derivativeGCD_polynomial_ne_zero v hv) (derivativeGCD_divisors v)

theorem squarefreeVector_squarefree {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0) :
    Squarefree (polynomial (squarefreeVector v)) := by
  rw [squarefreeVector_polynomial]
  exact quotient_squarefree_of_gcd ((polynomial_eq_zero_iff v).not.mpr hv)
    (derivativeGCD_polynomial_ne_zero v hv) (derivativeGCD_divisors v)

theorem squarefreeVector_separable {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0) :
    (polynomial (squarefreeVector v)).Separable :=
  PerfectField.separable_iff_squarefree.mpr (squarefreeVector_squarefree v hv)

theorem squarefreeVector_common_divisor_isUnit {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    (a : ℚ[X]) (ha : a ∣ polynomial (squarefreeVector v))
    (had : a ∣ (polynomial (squarefreeVector v)).derivative) : IsUnit a :=
  (squarefreeVector_separable v hv).isUnit_of_dvd' ha had

theorem squarefreeVector_derivative_ne_zero {n : ℕ} (v : Fin n → ℚ)
    (hdegree : (polynomial (squarefreeVector v)).natDegree ≠ 0) :
    (polynomial (squarefreeVector v)).derivative ≠ 0 :=
  Polynomial.derivative_ne_zero.mpr hdegree

theorem squarefreeVector_natDegree_le {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0) :
    (polynomial (squarefreeVector v)).natDegree ≤ (polynomial v).natDegree := by
  rw [squarefreeVector_polynomial]
  exact quotient_natDegree_le_of_gcd ((polynomial_eq_zero_iff v).not.mpr hv)
    (derivativeGCD_divisors v)

theorem squarefreeVector_eval₂_zero_iff {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    {K : Type*} [Field K] [CharZero K] (φ : ℚ →+* K) (z : K) :
    (polynomial (squarefreeVector v)).eval₂ φ z = 0 ↔ (polynomial v).eval₂ φ z = 0 := by
  rw [squarefreeVector_polynomial]
  exact quotient_eval₂_zero_iff_of_gcd ((polynomial_eq_zero_iff v).not.mpr hv)
    (derivativeGCD_polynomial_ne_zero v hv) (derivativeGCD_divisors v) φ z

theorem squarefreeVector_real_roots {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0) (x : ℝ) :
    (polynomial (squarefreeVector v)).eval₂ (algebraMap ℚ ℝ) x = 0 ↔
      (polynomial v).eval₂ (algebraMap ℚ ℝ) x = 0 :=
  squarefreeVector_eval₂_zero_iff v hv _ x

theorem squarefreeVector_complex_roots {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0) (z : ℂ) :
    (polynomial (squarefreeVector v)).eval₂ (algebraMap ℚ ℂ) z = 0 ↔
      (polynomial v).eval₂ (algebraMap ℚ ℂ) z = 0 :=
  squarefreeVector_eval₂_zero_iff v hv _ z

end
end Paper2.ExactInput.FixedRootCodec.VariablePolynomial
