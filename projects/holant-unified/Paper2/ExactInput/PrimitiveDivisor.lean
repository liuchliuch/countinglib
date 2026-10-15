import Paper2.ExactInput.AnnihilatorHeight
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! Primitive integral representatives of genuine monic rational factors.
Used only for mathematical size bounds, with no algorithm or decision procedure
asserted for the normalization choice. -/
namespace Paper2.ExactInput
open Polynomial

/-- A monic rational polynomial has a primitive integer representative, whose
leading coefficient is exactly the scale converting it back to monic form. -/
theorem primitive_integer_representative (q : Polynomial ℚ) (hq : q.Monic) :
    ∃ g : Polynomial ℤ, g.IsPrimitive ∧
      g.map (Int.castRingHom ℚ) = C (g.leadingCoeff : ℚ) * q := by
  let N := IsLocalization.integerNormalization (nonZeroDivisors ℤ) q
  obtain ⟨b, hb, hn⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) q
  change N.map (algebraMap ℤ ℚ) = b • q at hn
  have hN : N ≠ 0 := by
    intro h
    rw [h, Polynomial.map_zero] at hn
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hb
    have he : b • q = (b : ℚ) • q := by ext i; simp
    rw [he] at hn
    exact hq.ne_zero ((smul_eq_zero.mp hn.symm).resolve_left hb')
  refine ⟨N.primPart, N.isPrimitive_primPart, ?_⟩
  have hc : N.content ≠ 0 := mt Polynomial.content_eq_zero_iff.mp hN
  have hcc : (N.content : ℚ) ≠ 0 := by exact_mod_cast hc
  have hcp : C (N.content : ℚ) ≠ (0 : Polynomial ℚ) := C_ne_zero.mpr hcc
  have hm : C (N.content : ℚ) * N.primPart.map (Int.castRingHom ℚ) = C (b : ℚ) * q := by
    calc
      _ = (C N.content * N.primPart).map (Int.castRingHom ℚ) := by
        rw [Polynomial.map_mul, Polynomial.map_C]; rfl
      _ = N.map (Int.castRingHom ℚ) := congrArg (Polynomial.map (Int.castRingHom ℚ))
        N.eq_C_content_mul_primPart.symm
      _ = C (b : ℚ) * q := by
        simpa [Algebra.smul_def, Polynomial.algebraMap_apply] using hn
  have hl : (N.content : ℚ) * (N.primPart.leadingCoeff : ℚ) = b := by
    have h := congrArg Polynomial.leadingCoeff hm
    simpa only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hq.leadingCoeff, mul_one, Int.coe_castRingHom,
      Polynomial.leadingCoeff_map_of_injective (Int.castRingHom ℚ).injective_int] using h
  apply mul_left_cancel₀ hcp
  rw [hm, ← mul_assoc, ← C_mul, hl]

/-- A rational monic factor yields a genuine integer factor of every integer
multiple of the original polynomial. Gauss's lemma supplies actual divisibility. -/
theorem primitive_integer_factor {q : Polynomial ℚ} (hq : q.Monic)
    {p : Polynomial ℤ} (hd : q ∣ p.map (Int.castRingHom ℚ)) :
    ∃ g : Polynomial ℤ, g.IsPrimitive ∧ g ∣ p ∧
      g.map (Int.castRingHom ℚ) = C (g.leadingCoeff : ℚ) * q := by
  obtain ⟨g, hg, he⟩ := primitive_integer_representative q hq
  refine ⟨g, hg, ?_, he⟩
  apply hg.dvd_of_fraction_map_dvd_fraction_map (K := ℚ)
  change g.map (Int.castRingHom ℚ) ∣ p.map (Int.castRingHom ℚ)
  rw [he]
  have hu : IsUnit (C (g.leadingCoeff : ℚ) : Polynomial ℚ) := isUnit_C.mpr
    (isUnit_iff_ne_zero.mpr (by
      exact_mod_cast Polynomial.leadingCoeff_ne_zero.mpr hg.ne_zero))
  exact (IsUnit.mul_left_dvd hu).mpr hd

end Paper2.ExactInput
