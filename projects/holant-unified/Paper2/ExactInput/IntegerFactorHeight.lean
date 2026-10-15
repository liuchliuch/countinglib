import Paper2.ExactInput.PrimitiveDivisor
import Mathlib.NumberTheory.MahlerMeasure
import Mathlib.Data.Nat.Choose.Bounds

/-! Quantitative integer-factor coefficient bounds, using the library proof of
Mignotte's inequality. In particular a primitive numerator of a monic rational
factor cannot have arbitrarily large coefficients compared with its parent. -/
namespace Paper2.ExactInput
open Polynomial
open scoped BigOperators

/-- A deliberately coarse integral Mignotte bound, convenient for binary sizes. -/
theorem integer_factor_coeff_bound {p g : Polynomial ℤ} (hp : p ≠ 0) (hgp : g ∣ p)
    (j : ℕ) :
    (g.coeff j).natAbs ≤ 2 ^ p.natDegree * ∑ i ∈ p.support, (p.coeff i).natAbs := by
  obtain ⟨h, he⟩ := hgp
  have hh : h ≠ 0 := by intro hh; simp [hh] at he; exact hp he
  have hgdeg : g.natDegree ≤ p.natDegree := natDegree_le_of_dvd ⟨h, he⟩ hp
  have hchoose : g.natDegree.choose j ≤ 2 ^ p.natDegree :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by omega) hgdeg)
  let f : ℤ →+* ℂ := Int.castRingHom ℂ
  have hm := norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure j
    (g.map f) (h.map f) (Polynomial.one_le_mahlerMeasure_of_ne_zero hh)
  rw [← Polynomial.map_mul, ← he] at hm
  have hma := mahlerMeasure_le_sum_norm_coeff (p.map f)
  have hsum : (p.map f).sum (fun _ a => ‖a‖) =
      ((∑ i ∈ p.support, (p.coeff i).natAbs : ℕ) : ℝ) := by
    rw [Polynomial.sum_def, Polynomial.support_map_of_injective _ f.injective_int]
    simp only [Polynomial.coeff_map, f, Int.coe_castRingHom, Complex.norm_intCast,
      Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs]
  rw [hsum] at hma
  have hch : ((g.map f).natDegree.choose j : ℝ) ≤ (2 ^ p.natDegree : ℕ) := by
    rw [Polynomial.natDegree_map_eq_of_injective f.injective_int]
    exact_mod_cast hchoose
  have hr := hm.trans (mul_le_mul hch hma (mahlerMeasure_nonneg _)
    (by positivity : (0 : ℝ) ≤ (2 ^ p.natDegree : ℕ)))
  have hl : ‖(g.map f).coeff j‖ = ((g.coeff j).natAbs : ℝ) := by
    simp only [Polynomial.coeff_map, f, Int.coe_castRingHom, Complex.norm_intCast,
      Nat.cast_natAbs, Int.cast_abs]
  rw [hl] at hr
  exact_mod_cast hr

end Paper2.ExactInput
