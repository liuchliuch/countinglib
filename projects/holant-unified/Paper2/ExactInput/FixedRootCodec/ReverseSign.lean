import Paper2.ExactInput.FixedRootCodec.ReverseLinear
import Paper2.ExactInput.FixedFamilyField
import Paper2.ExactInput.LinearCombinationAnnihilator
import Mathlib.Algebra.Algebra.Hom.Rat

/-! Exact signs of variable rational linear combinations of fixed real
algebraic constants. Equality is tested in the derived fixed number field.
For nonzero values a proved annihilator height bound selects finite dyadic
precision, so signs do not require an unbounded root-refinement search. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, IsAlgebraic ℚ (a i))

def realLinearValue (v : Fin n → ℚ) : ℝ := ∑ i, (v i : ℝ)*a i

def realLinearCoordinates (v : Fin n → ℚ) : Fin (Module.finrank ℚ (familyField a)) → ℚ :=
  fun j => ∑ i, v i*familyCoordinates a ha i j

def realLinearCoordinatesComputes :
    Computes (vectorEncoding n) (vectorEncoding (Module.finrank ℚ (familyField a)))
      (realLinearCoordinates a ha) :=
  assembleComputes (vectorEncoding n) _ (realLinearCoordinates a ha) (fun j =>
    BellMachines.rationalProvider.sumComputes (vectorEncoding n) n
      (fun v i => v i*familyCoordinates a ha i j) (fun i =>
        BellMachines.rationalProvider.mulComputes (coordinateComputes n i)
          (constantComputes (vectorEncoding n) rationalEncoding (familyCoordinates a ha i j))))

theorem realLinearCoordinates_value (v : Fin n → ℚ) :
    ((familyPresentation a ha).decode (realLinearCoordinates a ha v) : ℝ)=realLinearValue a v := by
  have hv : realLinearCoordinates a ha v=∑ i, v i • familyCoordinates a ha i := by
    funext j
    simp [realLinearCoordinates]
  rw [hv,map_sum]
  simp only [map_smul]
  change (familyField a).subtype (∑ i, v i • (familyPresentation a ha).decode
    (familyCoordinates a ha i))=realLinearValue a v
  simp only [map_sum,realLinearValue,Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul]
  change (v i : ℝ)*((familyPresentation a ha).decode (familyCoordinates a ha i) : ℝ)=_
  rw [familyCoordinates_spec]

theorem realLinearCoordinates_zero_iff (v : Fin n → ℚ) :
    realLinearCoordinates a ha v=0 ↔ realLinearValue a v=0 := by
  have hinj : Function.Injective (fun w => ((familyPresentation a ha).decode w : ℝ)) :=
    Subtype.val_injective.comp (familyPresentation a ha).decode.injective
  have hz := hinj.eq_iff (a := realLinearCoordinates a ha v) (b := 0)
  simpa only [realLinearCoordinates_value,map_zero,ZeroMemClass.coe_zero] using hz.symm

def realLinearZeroComputes :
    Computes (vectorEncoding n) encodingBoolBool (fun v => decide (realLinearValue a v=0)) :=
  congrComputes ((realLinearCoordinatesComputes a ha).andThen
    (zeroComputes (vectorEncoding (Module.finrank ℚ (familyField a)))))
    (fun v => by simp only [Function.comp_apply,realLinearCoordinates_zero_iff])

include ha in
theorem realLinear_nonzero_bound :
    ∃ C : ℕ, ∀ (B : ℕ) (v : Fin n → ℚ), (∀ i, rationalBitHeight (v i)≤B) →
      realLinearValue a v≠0 →
      1≤|realLinearValue a v| * (2 : ℝ)^(2*(C*(B+1))+1) := by
  let F := familyPresentation a ha
  let c := fieldCoefficient a
  obtain ⟨C,hC⟩ := combinationAnnihilator_height_bound F.basis c
  refine ⟨C,fun B v hv hn => ?_⟩
  let p := combinationAnnihilator F.basis c v
  let e : familyField a →ₐ[ℚ] ℂ := Complex.ofRealHom.toRatAlgHom.comp (familyField a).val
  have hvalue : e (∑ i, v i • c i)=(realLinearValue a v : ℂ) := by
    simp [e,c,fieldCoefficient,realLinearValue,Algebra.smul_def,Complex.ofReal_sum]
  have hr : Polynomial.aeval (realLinearValue a v : ℂ) p=0 := by
    rw [← hvalue,Polynomial.aeval_algHom_apply]
    exact congrArg e (combinationAnnihilator_aeval F.basis c v)
  have hz : (realLinearValue a v : ℂ)≠0 := by exact_mod_cast hn
  have h := nonzero_root_norm_lower (combinationAnnihilator_monic F.basis c v).ne_zero
    (hC B v hv) hz hr
  simpa only [Complex.norm_real,Real.norm_eq_abs] using h

def realLinearSignExponent : ℕ := Classical.choose (realLinear_nonzero_bound a ha)

theorem realLinearSignExponent_bound (B : ℕ) (v : Fin n → ℚ)
    (hv : ∀ i, rationalBitHeight (v i)≤B) (hn : realLinearValue a v≠0) :
    1≤|realLinearValue a v| * (2 : ℝ)^(2*(realLinearSignExponent a ha*(B+1))+1) :=
  Classical.choose_spec (realLinear_nonzero_bound a ha) B v hv hn

def realLinearBrackets : ∀ i, RealBracket (a i) :=
  fun i => Classical.choice (realBracket_exists (a i) (ha i))

def realLinearSignPrecision (v : Fin n → ℚ) : ℕ :=
  2*realLinearSignExponent a ha*(((vectorEncoding n).encode v).length+2)+2

def realLinearSignPoint (v : Fin n → ℚ) : ℚ :=
  linearPoint (realLinearBrackets a ha) (realLinearSignPrecision a ha v) v

def realLinearSignPointComputes : Computes (vectorEncoding n) rationalEncoding (realLinearSignPoint a ha) := by
  let counter := precisionComputes (vectorEncoding n) (2*realLinearSignExponent a ha)
    (4*realLinearSignExponent a ha+2)
  exact congrComputes ((pairComputes counter (identityComputes (vectorEncoding n))).andThen
    (linearPointComputes (realLinearBrackets a ha)))
    (fun v => by
      simp only [Function.comp_apply,id_eq,realLinearSignPoint,realLinearSignPrecision]
      congr 1 <;> ring)

theorem realLinearSignPoint_accuracy (v : Fin n → ℚ) (hn : realLinearValue a v≠0) :
    |(realLinearSignPoint a ha v : ℝ)-realLinearValue a v| < |realLinearValue a v| := by
  let B := ((vectorEncoding n).encode v).length+1
  let H := realLinearSignExponent a ha*(B+1)
  have hb := realLinearSignExponent_bound a ha B v (coordinate_height_input v) hn
  have he : |(realLinearSignPoint a ha v : ℝ)-realLinearValue a v| <
      1/(2 : ℝ)^(realLinearSignPrecision a ha v) := by
    simpa only [realLinearSignPoint,realLinearValue] using
      linearPoint_error (realLinearBrackets a ha) (realLinearSignPrecision a ha v) v
  have hs : realLinearSignPrecision a ha v=2*H+2 := by
    simp only [realLinearSignPrecision,H,B]
    ring
  have hl : 1/(2 : ℝ)^(2*H+1)≤|realLinearValue a v| :=
    (div_le_iff₀ (by positivity)).mpr hb
  have hp : (2 : ℝ)^(2*H+1)≤(2 : ℝ)^(2*H+2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hi : 1/(2 : ℝ)^(2*H+2)≤1/(2 : ℝ)^(2*H+1) :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hp)
  rw [hs] at he
  exact he.trans_le (hi.trans hl)

theorem realLinearSignPoint_negative_iff (v : Fin n → ℚ) (hn : realLinearValue a v≠0) :
    realLinearSignPoint a ha v<0 ↔ realLinearValue a v<0 := by
  have he := realLinearSignPoint_accuracy a ha v hn
  have hreal : (realLinearSignPoint a ha v : ℝ)<0 ↔ realLinearValue a v<0 := by
    obtain ⟨hl,hu⟩ := abs_lt.mp he
    by_cases hv : realLinearValue a v<0
    · rw [abs_of_neg hv] at hu
      exact ⟨fun _ => hv,fun _ => by linarith⟩
    · have hp : 0<realLinearValue a v := lt_of_le_of_ne (le_of_not_gt hv) hn.symm
      rw [abs_of_pos hp] at hl
      exact ⟨fun h => by linarith,fun h => (hv h).elim⟩
  have hc : realLinearSignPoint a ha v<0 ↔ (realLinearSignPoint a ha v : ℝ)<0 := by
    exact_mod_cast (Iff.rfl : realLinearSignPoint a ha v<0 ↔ realLinearSignPoint a ha v<0)
  exact hc.trans hreal

/-- Unconditional exact sign machine for the fixed algebraic real coefficient
family; no accuracy certificate is supplied by the runtime caller. -/
def realLinearNegativeComputes :
    Computes (vectorEncoding n) encodingBoolBool (fun v => decide (realLinearValue a v<0)) := by
  let w := ifComputes (realLinearZeroComputes a ha)
    (constantComputes (vectorEncoding n) encodingBoolBool false)
    ((realLinearSignPointComputes a ha).andThen rationalNegativeComputes)
  apply congrComputes w
  intro v
  by_cases hn : realLinearValue a v=0
  · simp [hn]
  · simp only [Function.comp_apply,decide_eq_true_eq,if_neg hn]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using realLinearSignPoint_negative_iff a ha v hn

end
end Paper2.ExactInput.FixedRootCodec
