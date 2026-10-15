import Paper2.ExactInput.OutputMagnitude
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Algebra.Polynomial.Reverse

/-! A nonzero root of any nonzero rational polynomial with B-bit coefficients
cannot be smaller than 2^(-(2B+1)). Reversing the polynomial handles zero constant
coefficients, so the result also applies to difference annihilators with a zero root. -/
namespace Paper2.ExactInput
open Paper2.Algebraic Polynomial

lemma rationalBitHeight_inv_le (q : ℚ) : rationalBitHeight q⁻¹ ≤ rationalBitHeight q := by
  apply Nat.size_le_size
  unfold rationalHeight
  rw [Rat.num_inv, Rat.den_inv, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_sign]
  split_ifs with h
  · simp only [zero_mul, max_eq_right (by omega : 0 ≤ 1)]
    exact (Nat.one_le_iff_ne_zero.mpr q.den_pos.ne').trans (le_max_right _ _)
  · simp only [one_mul, max_comm]
    exact le_rfl

lemma rational_norm_le_pow {q : ℚ} {B : ℕ} (h : rationalBitHeight q ≤ B) :
    ‖(q : ℂ)‖ ≤ (2 : ℝ) ^ B := by
  apply (rational_norm_le_numerator q).trans
  have hn : q.num.natAbs ≤ 2 ^ B := (le_max_left _ _).trans (Nat.size_le.mp h).le
  exact_mod_cast hn

lemma rational_cauchyBound_le {p : Polynomial ℚ} {B : ℕ}
    (hp : ∀ j, rationalBitHeight (p.coeff j) ≤ B) :
    (p.map (Rat.castHom ℂ)).cauchyBound ≤ (2 : NNReal) ^ (2 * B + 1) := by
  have hc : ∀ j, ‖(p.map (Rat.castHom ℂ)).coeff j‖₊ ≤ (2 : NNReal) ^ B := by
    intro j
    rw [Polynomial.coeff_map]
    change ‖((p.coeff j : ℚ) : ℂ)‖ ≤ (2 : ℝ) ^ B
    exact rational_norm_le_pow (hp j)
  have hl : ‖(p.map (Rat.castHom ℂ)).leadingCoeff‖₊⁻¹ ≤ (2 : NNReal) ^ B := by
    rw [Polynomial.leadingCoeff_map_of_injective (Rat.castHom ℂ).injective]
    change ‖((p.leadingCoeff : ℚ) : ℂ)‖₊⁻¹ ≤ (2 : NNReal) ^ B
    have h := rational_norm_le_pow ((rationalBitHeight_inv_le p.leadingCoeff).trans (hp p.natDegree))
    simpa only [Rat.cast_inv, nnnorm_inv] using (show ‖((p.leadingCoeff⁻¹ : ℚ) : ℂ)‖₊ ≤
      (2 : NNReal) ^ B by
        change ‖((p.leadingCoeff⁻¹ : ℚ) : ℂ)‖ ≤ (2 : ℝ) ^ B
        exact h)
  have hs : (Finset.range (p.map (Rat.castHom ℂ)).natDegree).sup
      (fun j => ‖(p.map (Rat.castHom ℂ)).coeff j‖₊) ≤ (2 : NNReal) ^ B :=
    Finset.sup_le (fun j _ => hc j)
  unfold Polynomial.cauchyBound
  rw [div_eq_mul_inv]
  calc
    _ ≤ (2 : NNReal) ^ B * 2 ^ B + 1 := add_le_add (mul_le_mul' hs hl) le_rfl
    _ ≤ 2 ^ (2 * B + 1) := by
      rw [pow_add, pow_one, two_mul, pow_add]
      have hh : (1 : NNReal) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
      nlinarith

/-- A lower bound with no divisions, useful for selecting a finite rational grid. -/
theorem nonzero_root_norm_lower {p : Polynomial ℚ} (hp0 : p ≠ 0) {B : ℕ}
    (hp : ∀ j, rationalBitHeight (p.coeff j) ≤ B) {z : ℂ} (hz : z ≠ 0)
    (hroot : Polynomial.aeval z p = 0) :
    1 ≤ ‖z‖ * (2 : ℝ) ^ (2 * B + 1) := by
  letI : Invertible z := invertibleOfNonzero hz
  have hr : (p.reverse.map (Rat.castHom ℂ)).IsRoot z⁻¹ := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    simpa only [invOf_eq_inv] using
      (Polynomial.eval₂_reverse_eq_zero_iff (Rat.castHom ℂ) z p).mpr hroot
  have hrev : p.reverse ≠ 0 := mt Polynomial.reverse_eq_zero.mp hp0
  have hm : p.reverse.map (Rat.castHom ℂ) ≠ 0 :=
    Polynomial.map_ne_zero hrev
  have hb := (hr.norm_lt_cauchyBound hm).le.trans
    (rational_cauchyBound_le (fun j => by rw [Polynomial.coeff_reverse]; exact hp _))
  have hbn : ‖z⁻¹‖ ≤ (2 : ℝ) ^ (2 * B + 1) := by exact_mod_cast hb
  calc
    1 = ‖z‖ * ‖z⁻¹‖ := by rw [← norm_mul, mul_inv_cancel₀ hz, norm_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left hbn (norm_nonneg _)

end Paper2.ExactInput
