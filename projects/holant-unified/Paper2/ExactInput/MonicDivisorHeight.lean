import Paper2.ExactInput.IntegerFactorHeight
import Paper2.ExactInput.ClearedPolynomialHeight

/-! Rational monic factors inherit a linear coefficient bit-height bound from a
fixed-degree rational parent. The proof clears a real common denominator, uses
primitive integer factors and Mignotte, and normalizes by the integral leading
coefficient. No minimal polynomial or factoring algorithm is assumed. -/
namespace Paper2.ExactInput
open Paper2.Algebraic Polynomial
open scoped BigOperators

def factorMagnitudeBound (n B : ℕ) : ℕ :=
  2 ^ n * ((n + 1) * 2 ^ ((n + 2) * B))

theorem factorMagnitudeBound_size (n B : ℕ) :
    (factorMagnitudeBound n B).size ≤ n + (n + 1).size + (n + 2) * B + 2 := by
  have h₁ := natSize_mul_le (2 ^ n) ((n + 1) * 2 ^ ((n + 2) * B))
  have h₂ := natSize_mul_le (n + 1) (2 ^ ((n + 2) * B))
  rw [Nat.size_pow] at h₁ h₂
  unfold factorMagnitudeBound
  omega

theorem monic_divisor_height_bound (n B : ℕ) {p q : Polynomial ℚ}
    (hpdeg : p.natDegree ≤ n) (hp0 : p ≠ 0)
    (hp : ∀ j, rationalBitHeight (p.coeff j) ≤ B) (hq : q.Monic) (hqp : q ∣ p)
    (j : ℕ) : rationalBitHeight (q.coeff j) ≤ n + (n + 1).size + (n + 2) * B + 2 := by
  have hclear : q ∣ (clearedPolynomial n p).map (Int.castRingHom ℚ) := by
    rw [clearedPolynomial_map n p hpdeg]
    exact dvd_mul_of_dvd_right hqp _
  obtain ⟨g, hg, hgdiv, he⟩ := primitive_integer_factor hq hclear
  have hc0 := clearedPolynomial_ne_zero n hpdeg hp0
  have hcoef : ∀ k, (g.coeff k).natAbs ≤ factorMagnitudeBound n B := by
    intro k
    have hi := integer_factor_coeff_bound hc0 hgdiv k
    apply hi.trans
    exact Nat.mul_le_mul
      (Nat.pow_le_pow_right (by omega) (clearedPolynomial_natDegree_le n p))
      (clearedPolynomial_sum_coeff_le n B p hp)
  have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg.ne_zero
  have hrat : q.coeff j = Rat.divInt (g.coeff j) g.leadingCoeff := by
    have h := congrArg (fun r : Polynomial ℚ => r.coeff j) he
    simp only [coeff_map, coeff_C_mul, Int.coe_castRingHom] at h
    rw [Rat.divInt_eq_div]
    apply (eq_div_iff (by exact_mod_cast hlc)).mpr
    exact (mul_comm _ _).trans h.symm
  have hheight : rationalHeight (q.coeff j) ≤ factorMagnitudeBound n B := by
    rw [hrat]
    apply max_le
    · exact (divInt_num_le _ _ hlc).trans (hcoef j)
    · exact (divInt_den_le _ _ hlc).trans (hcoef g.natDegree)
  exact (Nat.size_le_size hheight).trans (factorMagnitudeBound_size n B)

end Paper2.ExactInput
