import ComplexCSP.Complexity.CountRecovery

/-! A genuine fixed-field FP decoder for exact natural-number outputs. -/
namespace ComplexCSP.ComplexityNaturalDecoder
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
  PlanarHom.ArithmeticCircuitPrimitives
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

private theorem exists_one_coordinate : ∃ j, basis.equivFun (1 : K) j ≠ 0 := by
  by_contra! h
  have hz : basis.equivFun (1 : K) = basis.equivFun 0 := by
    funext j
    simpa using h j
  exact one_ne_zero (basis.equivFun.injective hz)

/-- One fixed, nonzero coordinate of the field unit; this is program data. -/
noncomputable def coordinate : Fin dimension := Classical.choose (exists_one_coordinate basis)
theorem coordinate_ne_zero : basis.equivFun (1 : K) (coordinate basis) ≠ 0 :=
  Classical.choose_spec (exists_one_coordinate basis)

/-- Total decoding on arbitrary field elements. Only correctness on natural
casts is asserted; arbitrary nonintegral inputs need not be rejected. -/
noncomputable def decode (x : K) : ℕ :=
  ((basis.equivFun x (coordinate basis) /
    basis.equivFun (1 : K) (coordinate basis)).num).natAbs

@[simp] theorem decode_natCast (n : ℕ) : decode basis (n : K) = n := by
  have hcoord : basis.equivFun (n : K) (coordinate basis) =
      (n : ℚ) * basis.equivFun (1 : K) (coordinate basis) := by
    rw [← Nat.smul_one_eq_cast, map_nsmul]
    simp [Pi.smul_apply, nsmul_eq_mul]
  simp only [decode, hcoord, mul_div_cancel_right₀ _ (coordinate_ne_zero basis),
    Rat.num_natCast, Int.natAbs_natCast]

/-- Ordinary bit-polynomial decoding via a fixed coordinate, exact rational
normalization, numerator extraction and signed absolute-value conversion. -/
theorem fp_decode : FP (numberFieldEncoding basis) BitEncoding.nat (decode basis) := by
  have hc := FixedFieldArithmetic.fp_coordinate basis (coordinate basis)
  have hr := (hc.pair (fp_const (numberFieldEncoding basis) BitEncoding.rat
    (basis.equivFun (1 : K) (coordinate basis)))).comp RationalCircuits.fp_rational_division
  exact (hr.comp fp_rat_num).comp fp_int_natAbs

/-- Natural oracle answers can be embedded back into the fixed field by actual
binary-rational multiplication and fixed coordinate assembly. -/
theorem fp_natCast : FP BitEncoding.nat (numberFieldEncoding basis) (fun n : ℕ => (n : K)) := by
  apply FixedFieldArithmetic.fp_of_coordinates basis
  intro i
  have hq := fp_nat_int.comp fp_int_rat
  have hc := (hq.pair (fp_const BitEncoding.nat BitEncoding.rat (basis.equivFun (1 : K) i))).comp
    BinaryArithmetic.fp_rational_multiplication
  apply hc.congr
  intro n
  rw [← Nat.smul_one_eq_cast, map_nsmul]
  simp [Pi.smul_apply, nsmul_eq_mul]

end ComplexCSP.ComplexityNaturalDecoder
