import Paper2.ExactInput.Bounds.RationalHeight
import Paper2.ExactInput.NonzeroRootBound

/-! The real coordinate input words themselves bound coefficient height.
No externally supplied size annotation is used to select output precision. -/
namespace Paper2.ExactInput.FixedRootCodec
open Paper2.Algebraic Computability

theorem numerator_abs_le_code (q : ℚ) : q.num.natAbs ≤ rationalCode q + 1 := by
  have h := Nat.left_le_pair (Equiv.intEquivNat q.num) q.den
  have hi : q.num.natAbs ≤ Equiv.intEquivNat q.num + 1 := by
    cases q.num with
    | ofNat n => change n ≤ 2*n+1; omega
    | negSucc n => change n+1 ≤ 2*n+1+1; omega
  exact hi.trans (Nat.add_le_add_right h 1)

theorem rational_height_input (q : ℚ) :
    rationalBitHeight q ≤ (rationalEncoding.encode q).length + 1 := by
  have hn := numerator_abs_le_code q
  have hd := Nat.right_le_pair (Equiv.intEquivNat q.num) q.den
  change q.den ≤ rationalCode q at hd
  have hc : rationalCode q < 2 ^ (rationalEncoding.encode q).length := by
    change rationalCode q < 2 ^ (encodeNat (rationalCode q)).length
    rw [encodeNat_length]
    exact Nat.lt_size_self _
  apply Nat.size_le.mpr
  unfold rationalHeight
  rw [pow_succ]
  have hpos : 0 < 2 ^ (rationalEncoding.encode q).length := by positivity
  apply max_lt <;> omega

theorem coordinate_height_input {n : ℕ} (v : Fin n → ℚ) (i : Fin n) :
    rationalBitHeight (v i) ≤ ((vectorEncoding n).encode v).length + 1 := by
  have hi : 2 * (rationalEncoding.encode (v i)).length + 1 ≤
      ((vectorEncoding n).encode v).length := by
    rw [vectorEncoding,vectorEncode_length]
    exact Finset.single_le_sum
      (f := fun j : Fin n => 2 * (rationalEncoding.encode (v j)).length + 1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hr := rational_height_input (v i)
  omega

theorem rational_abs_le_pow {q : ℚ} {B : ℕ} (h : rationalBitHeight q ≤ B) :
    |q| ≤ (2 : ℚ)^B := by
  have hc := Paper2.ExactInput.rational_norm_le_pow h
  change ‖((q : ℝ) : ℂ)‖ ≤ (2 : ℝ)^B at hc
  have hc' : |(q : ℝ)| ≤ (2 : ℝ)^B := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hc
  exact_mod_cast hc'

end Paper2.ExactInput.FixedRootCodec
