import Counting.Algorithm.KarpLuby.Dyadic

/-!
# Executable rational accuracy and confidence budgets

All arithmetic below runs on the numerator and denominator of the requested
rational. The bounds concern numerical budgets; they do not assert a machine
runtime theorem for computing these budgets.
-/

namespace Counting.Algorithm.KarpLuby

/-- Strict integer upper approximation to `1 / epsilon` for positive epsilon. -/
def reciprocalCeiling (epsilon : ℚ) : ℕ :=
  epsilon.den / epsilon.num.toNat + 1

/-- The sample count includes the factor nine for a base radius `epsilon / 3`. -/
def samples (m : ℕ) (epsilon : ℚ) : ℕ :=
  144 * m * reciprocalCeiling epsilon ^ 2

/-- Half the number of independent groups in the confidence amplification. -/
def confidenceGroups (delta : ℚ) : ℕ :=
  Nat.size (reciprocalCeiling delta) + 1

 theorem reciprocalCeiling_pos (epsilon : ℚ) : 0 < reciprocalCeiling epsilon := by
  exact Nat.succ_pos _

 theorem positive_num_toNat {epsilon : ℚ} (he : 0 < epsilon) :
    0 < epsilon.num.toNat := by
  exact Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr he)

 theorem positive_rat_eq_num_toNat_div_den {epsilon : ℚ} (he : 0 < epsilon) :
    epsilon = (epsilon.num.toNat : ℚ) / epsilon.den := by
  have hn : (epsilon.num.toNat : ℤ) = epsilon.num :=
    Int.toNat_of_nonneg (Rat.num_pos.mpr he).le
  rw [← Int.cast_natCast, hn]
  exact epsilon.num_div_den.symm

 theorem inv_lt_reciprocalCeiling {epsilon : ℚ} (he : 0 < epsilon) :
    1 / epsilon < (reciprocalCeiling epsilon : ℚ) := by
  have hn := positive_num_toNat he
  have hnq : (0 : ℚ) < epsilon.num.toNat := by exact_mod_cast hn
  have hi : (1 / epsilon : ℚ) = epsilon.den / epsilon.num.toNat := by
    conv_lhs => rw [positive_rat_eq_num_toNat_div_den he]
    simp
  rw [hi, div_lt_iff₀ hnq]
  have h := Nat.lt_mul_div_succ epsilon.den hn
  have hc : (epsilon.den : ℚ) <
      (epsilon.num.toNat : ℚ) * (reciprocalCeiling epsilon : ℚ) := by
    exact_mod_cast h
  simpa [mul_comm] using hc

 theorem inv_le_reciprocalCeiling {epsilon : ℚ} (he : 0 < epsilon) :
    1 / epsilon ≤ (reciprocalCeiling epsilon : ℚ) :=
  (inv_lt_reciprocalCeiling he).le

/-- The chosen integer grows at most linearly in inverse relative accuracy. -/
theorem reciprocalCeiling_le_inv_add_one {epsilon : ℚ} (he : 0 < epsilon) :
    (reciprocalCeiling epsilon : ℚ) ≤ 1 / epsilon + 1 := by
  have hi : (1 / epsilon : ℚ) = epsilon.den / epsilon.num.toNat := by
    conv_lhs => rw [positive_rat_eq_num_toNat_div_den he]
    simp
  simp only [reciprocalCeiling, Nat.cast_add, Nat.cast_one, hi]
  simpa only [add_comm] using add_le_add_right (Nat.cast_div_le (α := ℚ)
    (m := epsilon.den) (n := epsilon.num.toNat)) 1

 theorem one_le_reciprocalCeiling_mul {epsilon : ℚ} (he : 0 < epsilon) :
    1 ≤ (reciprocalCeiling epsilon : ℚ) * epsilon :=
  (div_le_iff₀ he).mp (inv_le_reciprocalCeiling he)

 theorem reciprocalCeiling_inverse_le {epsilon : ℚ} (he : 0 < epsilon) :
    1 / (reciprocalCeiling epsilon : ℚ) ≤ epsilon := by
  apply (div_le_iff₀ (by exact_mod_cast reciprocalCeiling_pos epsilon)).mpr
  simpa [mul_comm] using one_le_reciprocalCeiling_mul he

 theorem samples_pos {m : ℕ} (hm : 0 < m) (epsilon : ℚ) :
    0 < samples m epsilon := by
  have := reciprocalCeiling_pos epsilon
  unfold samples
  positivity

/-- Exact hypothesis consumed by the variance-sensitive confidence theorem. -/
theorem samples_accuracy_budget (m : ℕ) {epsilon : ℚ} (he : 0 < epsilon) :
    144 * (m : ℚ) ≤ (samples m epsilon : ℚ) * epsilon ^ 2 := by
  have hsq : (1 : ℚ) ≤ ((reciprocalCeiling epsilon : ℚ) * epsilon) ^ 2 :=
    one_le_pow₀ (one_le_reciprocalCeiling_mul he)
  calc
    144 * (m : ℚ) ≤ 144 * (m : ℚ) *
        ((reciprocalCeiling epsilon : ℚ) * epsilon) ^ 2 := by
      exact le_mul_of_one_le_right (by positivity) hsq
    _ = _ := by simp only [samples, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]; ring

 theorem samples_le_inverse_polynomial (m : ℕ) {epsilon : ℚ} (he : 0 < epsilon) :
    (samples m epsilon : ℚ) ≤ 144 * (m : ℚ) * (1 / epsilon + 1) ^ 2 := by
  simp only [samples, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  gcongr
  exact reciprocalCeiling_le_inv_add_one he

 theorem confidenceGroups_pos (delta : ℚ) : 0 < confidenceGroups delta := by
  unfold confidenceGroups
  omega

 theorem reciprocalCeiling_le_confidence_pow (delta : ℚ) :
    reciprocalCeiling delta ≤ 2 ^ confidenceGroups delta := by
  have h := Nat.lt_size_self (reciprocalCeiling delta)
  simp only [confidenceGroups, pow_succ]
  omega

/-- The amplified failure bound meets the user's positive rational delta. -/
theorem confidenceGroups_failure_le {delta : ℚ} (hd : 0 < delta) :
    1 / (2 ^ confidenceGroups delta : ℚ) ≤ delta := by
  calc
    1 / (2 ^ confidenceGroups delta : ℚ) ≤
        1 / (reciprocalCeiling delta : ℚ) := by
      apply one_div_le_one_div_of_le
      · exact_mod_cast reciprocalCeiling_pos delta
      · exact_mod_cast reciprocalCeiling_le_confidence_pow delta
    _ ≤ delta := reciprocalCeiling_inverse_le hd

 theorem reciprocalCeiling_le_den_add_one (epsilon : ℚ) :
    reciprocalCeiling epsilon ≤ epsilon.den + 1 := by
  unfold reciprocalCeiling
  exact Nat.add_le_add_right (Nat.div_le_self _ _) 1

/-- Group count is bounded by the binary length of the encoded denominator. -/
theorem confidenceGroups_le_den_size (delta : ℚ) :
    confidenceGroups delta ≤ Nat.size delta.den + 2 := by
  have hc := Nat.size_le_size (reciprocalCeiling_le_den_add_one delta)
  have hp := Nat.lt_size_self delta.den
  have hs : Nat.size (delta.den + 1) ≤ Nat.size delta.den + 1 := by
    apply Nat.size_le.mpr
    rw [pow_succ]
    omega
  unfold confidenceGroups
  omega

end Counting.Algorithm.KarpLuby
