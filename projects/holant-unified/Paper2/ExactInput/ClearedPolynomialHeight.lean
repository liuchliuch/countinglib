import Paper2.ExactInput.Bounds.CommonDenominator
import Mathlib.Algebra.Polynomial.OfFn

/-! Explicit common-denominator integer polynomial, with its actual coefficient
magnitudes bounded from the rational input coefficient bit heights. -/
namespace Paper2.ExactInput
open Paper2.Algebraic Polynomial
open scoped BigOperators

def polynomialDenominator (n : ℕ) (p : Polynomial ℚ) : ℕ :=
  commonDenominator (fun i : Fin (n + 1) => p.coeff i.val)

def clearedPolynomial (n : ℕ) (p : Polynomial ℚ) : Polynomial ℤ :=
  Polynomial.ofFn (n + 1)
    (clearedNumerator (fun i : Fin (n + 1) => p.coeff i.val))

theorem polynomialDenominator_pos (n : ℕ) (p : Polynomial ℚ) :
    0 < polynomialDenominator n p := commonDenominator_pos _

theorem clearedPolynomial_natDegree_le (n : ℕ) (p : Polynomial ℚ) :
    (clearedPolynomial n p).natDegree ≤ n :=
  Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)

theorem clearedPolynomial_map (n : ℕ) (p : Polynomial ℚ) (hp : p.natDegree ≤ n) :
    (clearedPolynomial n p).map (Int.castRingHom ℚ) = C (polynomialDenominator n p : ℚ) * p := by
  ext j
  rw [coeff_map, coeff_C_mul]
  by_cases hj : j < n + 1
  · rw [clearedPolynomial, ofFn_coeff_eq_val_of_lt _ hj]
    have h := clearedNumerator_correct (fun i : Fin (n + 1) => p.coeff i.val) ⟨j, hj⟩
    change (_ : ℚ) / (polynomialDenominator n p : ℚ) = p.coeff j at h
    have hd : (polynomialDenominator n p : ℚ) ≠ 0 := by
      exact_mod_cast (polynomialDenominator_pos n p).ne'
    exact (div_eq_iff hd).mp h |>.trans (mul_comm _ _)
  · rw [clearedPolynomial, ofFn_coeff_eq_zero_of_ge _ (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

theorem clearedPolynomial_ne_zero (n : ℕ) {p : Polynomial ℚ}
    (hp : p.natDegree ≤ n) (hp0 : p ≠ 0) : clearedPolynomial n p ≠ 0 := by
  intro h
  have he := clearedPolynomial_map n p hp
  rw [h, Polynomial.map_zero] at he
  have hd : C (polynomialDenominator n p : ℚ) ≠ (0 : Polynomial ℚ) := by
    apply C_ne_zero.mpr
    exact_mod_cast (polynomialDenominator_pos n p).ne'
  exact hp0 ((mul_eq_zero.mp he.symm).resolve_left hd)

theorem polynomialDenominator_le (n B : ℕ) (p : Polynomial ℚ)
    (hp : ∀ j, rationalBitHeight (p.coeff j) ≤ B) :
    polynomialDenominator n p ≤ 2 ^ ((n + 1) * B) := by
  calc
    polynomialDenominator n p ≤ ∏ _i : Fin (n + 1), 2 ^ B := by
      unfold polynomialDenominator commonDenominator
      apply Finset.prod_le_prod
      intro i _
      exact (le_max_right _ _).trans (Nat.size_le.mp (hp i.val)).le
    _ = 2 ^ ((n + 1) * B) := by simp [← pow_mul, Nat.mul_comm]

theorem clearedPolynomial_coeff_le (n B : ℕ) (p : Polynomial ℚ)
    (hp : ∀ j, rationalBitHeight (p.coeff j) ≤ B) (j : ℕ) :
    ((clearedPolynomial n p).coeff j).natAbs ≤ 2 ^ ((n + 2) * B) := by
  by_cases hj : j < n + 1
  · rw [clearedPolynomial, ofFn_coeff_eq_val_of_lt _ hj]
    unfold clearedNumerator
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    have hnum : (p.coeff j).num.natAbs ≤ 2 ^ B :=
      (le_max_left _ _).trans (Nat.size_le.mp (hp j)).le
    have hden : commonDenominator (fun i : Fin (n + 1) => p.coeff i.val) /
        (p.coeff j).den ≤ 2 ^ ((n + 1) * B) :=
      (Nat.div_le_self _ _).trans (polynomialDenominator_le n B p hp)
    calc
      _ ≤ 2 ^ B * 2 ^ ((n + 1) * B) := Nat.mul_le_mul hnum hden
      _ = 2 ^ ((n + 2) * B) := by rw [← pow_add]; congr 1; ring
  · rw [clearedPolynomial, ofFn_coeff_eq_zero_of_ge _ (by omega)]
    simp

/-- The sum in the integer-factor bound has at most n+1 nonzero terms. -/
theorem clearedPolynomial_sum_coeff_le (n B : ℕ) (p : Polynomial ℚ)
    (hp : ∀ j, rationalBitHeight (p.coeff j) ≤ B) :
    (∑ j ∈ (clearedPolynomial n p).support,
      ((clearedPolynomial n p).coeff j).natAbs) ≤ (n + 1) * 2 ^ ((n + 2) * B) := by
  let q := clearedPolynomial n p
  have hs : q.support ⊆ Finset.range (n + 1) := by
    intro j hj
    have h := le_natDegree_of_ne_zero (mem_support_iff.mp hj)
    change j ≤ (clearedPolynomial n p).natDegree at h
    exact Finset.mem_range.mpr (by have := clearedPolynomial_natDegree_le n p; omega)
  calc
    _ ≤ ∑ _j ∈ q.support, 2 ^ ((n + 2) * B) :=
      Finset.sum_le_sum (fun j _ => clearedPolynomial_coeff_le n B p hp j)
    _ = q.support.card * 2 ^ ((n + 2) * B) := by simp
    _ ≤ (n + 1) * 2 ^ ((n + 2) * B) := Nat.mul_le_mul_right _
      (by simpa using Finset.card_le_card hs)

end Paper2.ExactInput
