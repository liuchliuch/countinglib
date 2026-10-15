import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Integral primitive presentations of number fields

Semantic existence results supporting uniform encoded inputs. The power
basis and polynomial chosen here are proof objects, not a runtime field oracle.
-/
namespace ComplexCSP.AlgebraicEncoding

open Polynomial IntermediateField
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [CharZero K]

/-- Multiplying a generator by a nonzero rational leaves its generated field unchanged. -/
theorem adjoin_rat_mul (a : K) (q : ℚ) (hq : q ≠ 0) :
    ℚ⟮(q : K) * a⟯ = ℚ⟮a⟯ := by
  apply le_antisymm
  · apply adjoin_simple_le_iff.mpr
    exact ℚ⟮a⟯.mul_mem (ℚ⟮a⟯.algebraMap_mem q) (mem_adjoin_simple_self ℚ a)
  · apply adjoin_simple_le_iff.mpr
    have hm := ℚ⟮(q : K) * a⟯.mul_mem
      (ℚ⟮(q : K) * a⟯.algebraMap_mem q⁻¹)
      (mem_adjoin_simple_self ℚ ((q : K) * a))
    have hqK : (q : K) ≠ 0 := Rat.cast_ne_zero.mpr hq
    rw [map_inv₀] at hm
    change (q : K)⁻¹ * ((q : K) * a) ∈ ℚ⟮(q : K) * a⟯ at hm
    simpa only [inv_mul_cancel_left₀ hqK] using hm

/-- Every number field has an integral primitive element. -/
theorem exists_integral_primitive [NumberField K] :
    ∃ a : K, IsIntegral ℤ a ∧ ℚ⟮a⟯ = ⊤ := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element ℚ K
  obtain ⟨d, hi⟩ :=
    (IsIntegral.of_finite ℚ a).exists_multiple_integral_of_isLocalization ℤ⁰ a
  have hd : (d : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  refine ⟨(d : ℤ) • a, hi, ?_⟩
  have hq : ((d : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  simpa only [zsmul_eq_mul, Rat.cast_intCast] using
    (adjoin_rat_mul a ((d : ℤ) : ℚ) hq).trans ha

/-- A specified primitive element carries an actual rational power basis. -/
noncomputable def powerBasisOfPrimitive [NumberField K] (a : K)
    (ha : ℚ⟮a⟯ = ⊤) : PowerBasis ℚ K :=
  (adjoin.powerBasis (IsIntegral.of_finite ℚ a)).map
    ((IntermediateField.equivOfEq ha).trans IntermediateField.topEquiv)

@[simp] theorem powerBasisOfPrimitive_gen [NumberField K] (a : K)
    (ha : ℚ⟮a⟯ = ⊤) : (powerBasisOfPrimitive a ha).gen = a := by
  simp [powerBasisOfPrimitive, PowerBasis.map_gen, adjoin.powerBasis_gen,
    IntermediateField.AdjoinSimple.gen]

/-- The exact semantic data represented by a monic irreducible integer input polynomial. -/
structure IntegralPrimitivePresentation (K : Type*) [Field K] [NumberField K] where
  basis : PowerBasis ℚ K
  integral : IsIntegral ℤ basis.gen
  polynomial : ℤ[X]
  monic : polynomial.Monic
  irreducible : Irreducible polynomial
  map_eq_minpoly : polynomial.map (Int.castRingHom ℚ) = minpoly ℚ basis.gen

/-- Package a specified integral primitive element without changing its value. -/
noncomputable def integralPresentationOfPrimitive [NumberField K] (a : K)
    (hi : IsIntegral ℤ a) (ha : ℚ⟮a⟯ = ⊤) : IntegralPrimitivePresentation K where
  basis := powerBasisOfPrimitive a ha
  integral := by simpa using hi
  polynomial := minpoly ℤ a
  monic := minpoly.monic hi
  irreducible := minpoly.irreducible hi
  map_eq_minpoly := by
    rw [powerBasisOfPrimitive_gen]
    exact (minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hi).symm

@[simp] theorem integralPresentationOfPrimitive_gen [NumberField K] (a : K)
    (hi : IsIntegral ℤ a) (ha : ℚ⟮a⟯ = ⊤) :
    (integralPresentationOfPrimitive a hi ha).basis.gen = a :=
  powerBasisOfPrimitive_gen a ha

/-- Every number field admits a monic integral primitive presentation. -/
theorem exists_integralPrimitivePresentation [NumberField K] :
    Nonempty (IntegralPrimitivePresentation K) := by
  obtain ⟨a, hi, ha⟩ := exists_integral_primitive (K := K)
  let pb := powerBasisOfPrimitive a ha
  have hg : pb.gen = a := powerBasisOfPrimitive_gen a ha
  refine ⟨⟨pb, hg ▸ hi, minpoly ℤ a, minpoly.monic hi,
    minpoly.irreducible hi, ?_⟩⟩
  rw [hg]
  exact (minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hi).symm

end ComplexCSP.AlgebraicEncoding
