import Paper2.ExactInput.FixedRootCodec.ComplexRectangle
import Paper2.ExactInput.RootSeparation

/-! An unconditional actual finite-machine fixed-field rectangle codec.
Precision is selected from the true coordinate input bytes and the proved
fixed-field root separation. All roots on rational grid lines and the zero
value receive a strictly open isolating rectangle. -/
namespace Paper2.ExactInput.FixedRootCodec
set_option backward.isDefEq.respectTransparency false
open Computability Paper2.Algebraic Paper2.Complexity Polynomial
open BinaryCompose FixedFieldMachines GraphPreprocessing
open scoped BigOperators
noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}

def complexBasis (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) : Fin n → ℂ :=
  fun i => e (F.basis i)

theorem complexBasis_algebraic (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) (i : Fin n) :
    IsAlgebraic ℚ (complexBasis F e i) := by
  let v := F.decode.symm (F.basis i)
  have ha : IsIntegral ℚ (F.basis i) :=
    ⟨fixedAnnihilator F v,fixedAnnihilator_monic F v,
      by simpa only [v,F.decode.apply_symm_apply,Polynomial.aeval_def]
        using fixedAnnihilator_aeval F v⟩
  exact (ha.map e).isAlgebraic

theorem complexBasis_value (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) (v : Fin n → ℚ) :
    complexLinearValue (complexBasis F e) v = e (F.decode v) := by
  change _ = e (F.basis.equivFun.symm v)
  rw [F.basis.equivFun_symm_apply]
  simp [complexLinearValue,complexBasis,Algebra.smul_def]

def fieldPrecision (C D N : ℕ) : ℕ := (2*C+1)*N+4*C+D+4

theorem fieldPrecision_eq (C D N : ℕ) :
    fieldPrecision C D N = (N+1)+D+(2*(C*((N+1)+1))+1)+2 := by
  unfold fieldPrecision
  ring

theorem precision_ratio (E S : ℕ) :
    (2 : ℝ)^E / 2^(E+S+2) = 1/(4*2^S) := by
  rw [pow_add,pow_add,pow_two]
  have hE : (2 : ℝ)^E ≠ 0 := by positivity
  have hS : (2 : ℝ)^S ≠ 0 := by positivity
  field_simp
  <;> ring

theorem precision_small (S : ℕ) :
    1/(4*(2 : ℝ)^S)+1/(4*(2 : ℝ)^S) ≤ 6/(6*(2 : ℝ)^S) := by
  have h : (0 : ℝ) < 2^S := by positivity
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 6*2^S)).mpr
  have he : (1/(4*(2 : ℝ)^S)+1/(4*(2 : ℝ)^S))*(6*2^S) = 3 := by
    field_simp
    <;> ring
  rw [he]
  norm_num

structure FieldRectangleCodec (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) where
  rectangle : (Fin n → ℚ) → RationalRectangle
  computes : Computes (vectorEncoding n) rectangleEncoding rectangle
  contains : ∀ v, (rectangle v).Contains (e (F.decode v))
  isolates : ∀ v w, (rectangle v).Contains w →
    Polynomial.aeval w (minpoly ℚ (F.decode v)) = 0 → w = e (F.decode v)

def fieldRectangleCodec (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) : FieldRectangleCodec F e := by
  let b := complexBrackets (complexBasis F e) (complexBasis_algebraic F e)
  let C := Classical.choose (fixed_field_root_separation F)
  have hC := Classical.choose_spec (fixed_field_root_separation F)
  let D := Classical.choose (complexRectangle_width_bound b)
  have hD := Classical.choose_spec (complexRectangle_width_bound b)
  let rectangle := fun v : Fin n → ℚ =>
    complexRectangle b (fieldPrecision C D ((vectorEncoding n).encode v).length) v
  let counter := precisionComputes (vectorEncoding n) (2*C+1) (4*C+D+4)
  have computes : Computes (vectorEncoding n) rectangleEncoding rectangle :=
    congrComputes ((pairComputes counter (identityComputes (vectorEncoding n))).andThen
      (complexRectangleComputes b)) (fun v => by
        simp only [Function.comp_apply,id_eq,rectangle,fieldPrecision,Nat.add_assoc])
  have contains (v : Fin n → ℚ) : (rectangle v).Contains (e (F.decode v)) := by
    rw [← complexBasis_value F e v]
    exact complexRectangle_contains b _ v
  refine ⟨rectangle,computes,contains,?_⟩
  intro v w hw hr
  by_contra hne
  let N := ((vectorEncoding n).encode v).length
  let B := N+1
  let S := 2*(C*(B+1))+1
  have hv : ∀ i, rationalBitHeight (v i) ≤ B := coordinate_height_input v
  have hz : Polynomial.aeval (e (F.decode v)) (minpoly ℚ (F.decode v)) = 0 := by
    rw [← minpoly.algHom_eq e e.injective (F.decode v)]
    exact minpoly.aeval ℚ (e (F.decode v))
  have separated : (6 : ℝ)/(6*(2 : ℝ)^S) ≤ ‖w-e (F.decode v)‖ := by
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,S,C] using
      hC B v hv (e (F.decode v)) w hz hr hne
  have widths := hD (fieldPrecision C D N) B v hv
  change (rectangle v).reUpper - (rectangle v).reLower ≤ (2 : ℚ)^(B+D)/2^(fieldPrecision C D N) ∧
    (rectangle v).imUpper - (rectangle v).imLower ≤ (2 : ℚ)^(B+D)/2^(fieldPrecision C D N) at widths
  have hre : ((rectangle v).reUpper : ℝ) - (rectangle v).reLower ≤ 1/(4*(2 : ℝ)^S) := by
    have hr' := (Rat.cast_le (K := ℝ)).mpr widths.1
    push_cast at hr'
    rw [fieldPrecision_eq,show N+1 = B from rfl,show 2*(C*(B+1))+1 = S from rfl,
      precision_ratio] at hr'
    exact hr'
  have him : ((rectangle v).imUpper : ℝ) - (rectangle v).imLower ≤ 1/(4*(2 : ℝ)^S) := by
    have hi' := (Rat.cast_le (K := ℝ)).mpr widths.2
    push_cast at hi'
    rw [fieldPrecision_eq,show N+1 = B from rfl,show 2*(C*(B+1))+1 = S from rfl,
      precision_ratio] at hi'
    exact hi'
  have near := (rectangle_near (contains v) hw).trans_le
    ((add_le_add hre him).trans (precision_small S))
  exact (not_lt_of_ge separated) near

end
end Paper2.ExactInput.FixedRootCodec
