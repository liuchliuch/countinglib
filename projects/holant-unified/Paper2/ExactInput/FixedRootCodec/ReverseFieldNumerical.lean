import Paper2.ExactInput.FixedRootCodec.ReverseFieldEmbeddings
import Paper2.ExactInput.FixedRootCodec.ReverseLinear
import Paper2.ExactInput.FixedRootCodec.ComplexRectangle

/-! Fixed inverse embedding matrices have algebraic entries. The programs in
this file approximate each real inverse row and round the result on the exact
coordinate lattice. They operate on literal rational vectors and an explicit
precision word. Correctness is proved for a tuple approximating the actual
conjugates; generating that tuple from a varying polynomial is a separate
root-isolation task. No full root decoder is asserted here. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines GraphPreprocessing Polynomial Matrix
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] {n : ℕ}

def algebraicFieldEmbeddingMatrix (F : FixedField K n) :
    Matrix (Fin n) (Fin n) Paper2.Tractable.AlgebraicComplex :=
  fun i j => ⟨fieldEmbeddingMatrix F i j,
    ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (F.basis j)).algHom
      (embeddingEnumeration F i)).isIntegral⟩

theorem algebraicFieldEmbeddingMatrix_coe (F : FixedField K n) :
    (algebraicFieldEmbeddingMatrix F).map (algebraMap Paper2.Tractable.AlgebraicComplex ℂ) =
      fieldEmbeddingMatrix F := rfl

theorem algebraicFieldEmbeddingMatrix_det_ne_zero (F : FixedField K n) :
    (algebraicFieldEmbeddingMatrix F).det ≠ 0 := by
  intro h
  have hc := (algebraMap Paper2.Tractable.AlgebraicComplex ℂ).map_det
    (algebraicFieldEmbeddingMatrix F)
  rw [RingHom.mapMatrix_apply,algebraicFieldEmbeddingMatrix_coe,h,map_zero] at hc
  exact fieldEmbeddingMatrix_det_ne_zero F hc.symm

theorem inverseFieldEmbeddingMatrix_algebraic (F : FixedField K n) (i j : Fin n) :
    IsAlgebraic ℚ (inverseFieldEmbeddingMatrix F i j) := by
  let A := algebraicFieldEmbeddingMatrix F
  let f := algebraMap Paper2.Tractable.AlgebraicComplex ℂ
  have h : (fieldEmbeddingMatrix F)⁻¹ = (A⁻¹).map f := by
    apply Matrix.inv_eq_left_inv
    rw [← algebraicFieldEmbeddingMatrix_coe,← Matrix.map_mul]
    rw [Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr
      (algebraicFieldEmbeddingMatrix_det_ne_zero F)),Matrix.map_one f]
    all_goals simp [f]
  rw [inverseFieldEmbeddingMatrix,h]
  exact (A⁻¹ i j).property.isAlgebraic

def inverseRealRow (F : FixedField K n) (i : Fin n) : Fin n → ℝ :=
  fun j => (inverseFieldEmbeddingMatrix F i j).re

def inverseImaginaryRow (F : FixedField K n) (i : Fin n) : Fin n → ℝ :=
  fun j => -(inverseFieldEmbeddingMatrix F i j).im

def inverseRealBrackets (F : FixedField K n) (i : Fin n) :
    ∀ j, RealBracket (inverseRealRow F i j) :=
  fun j => Classical.choice (realBracket_exists _
    (algebraic_re _ (inverseFieldEmbeddingMatrix_algebraic F i j)))

def inverseImaginaryBrackets (F : FixedField K n) (i : Fin n) :
    ∀ j, RealBracket (inverseImaginaryRow F i j) :=
  fun j => Classical.choice (realBracket_exists _
    (algebraic_im _ (inverseFieldEmbeddingMatrix_algebraic F i j)).neg)

abbrev conjugatePointEncoding (n : ℕ) :=
  pairEncoding (vectorEncoding n) (vectorEncoding n)

abbrev inversePointInputEncoding (n : ℕ) :=
  pairEncoding UnaryBinary.unaryEncoding (conjugatePointEncoding n)

def rationalComplexPoint (vr vi : Fin n → ℚ) : Fin n → ℂ :=
  fun j => (vr j : ℂ) + (vi j : ℂ) * Complex.I

def inverseRowPoint (F : FixedField K n) (s : ℕ) (vr vi : Fin n → ℚ) (i : Fin n) : ℚ :=
  linearPoint (inverseRealBrackets F i) s vr +
    linearPoint (inverseImaginaryBrackets F i) s vi

def inverseRowPointComputes (F : FixedField K n) (i : Fin n) :
    Computes (inversePointInputEncoding n) rationalEncoding
      (fun p => inverseRowPoint F p.1 p.2.1 p.2.2 i) := by
  let s := Wiring.firstComputes UnaryBinary.unaryEncoding (conjugatePointEncoding n)
  let v := Wiring.secondComputes UnaryBinary.unaryEncoding (conjugatePointEncoding n)
  let vr := v.andThen (Wiring.firstComputes (vectorEncoding n) (vectorEncoding n))
  let vi := v.andThen (Wiring.secondComputes (vectorEncoding n) (vectorEncoding n))
  exact congrComputes (rationalProvider.addComputes
    ((pairComputes s vr).andThen (linearPointComputes (inverseRealBrackets F i)))
    ((pairComputes s vi).andThen (linearPointComputes (inverseImaginaryBrackets F i))))
    (fun _ => rfl)

def inversePointComputes (F : FixedField K n) :
    Computes (inversePointInputEncoding n) (vectorEncoding n)
      (fun p i => inverseRowPoint F p.1 p.2.1 p.2.2 i) :=
  assembleComputes _ n _ (inverseRowPointComputes F)

theorem inverse_row_real (F : FixedField K n) (vr vi : Fin n → ℚ) (i : Fin n) :
    ((inverseFieldEmbeddingMatrix F *ᵥ rationalComplexPoint vr vi) i).re =
      (∑ j, (vr j : ℝ) * inverseRealRow F i j) +
      (∑ j, (vi j : ℝ) * inverseImaginaryRow F i j) := by
  simp [Matrix.mulVec,dotProduct,rationalComplexPoint,Complex.mul_re,
    inverseRealRow,inverseImaginaryRow,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    mul_comm,sub_eq_add_neg]

theorem inverseRowPoint_error (F : FixedField K n) (s : ℕ)
    (vr vi : Fin n → ℚ) (i : Fin n) :
    |(inverseRowPoint F s vr vi i : ℝ) -
      ((inverseFieldEmbeddingMatrix F *ᵥ rationalComplexPoint vr vi) i).re| <
      2/(2 : ℝ)^s := by
  have hr := linearPoint_error (inverseRealBrackets F i) s vr
  have hi := linearPoint_error (inverseImaginaryBrackets F i) s vi
  rw [inverse_row_real]
  unfold inverseRowPoint
  push_cast
  have ht := abs_add_le
    ((linearPoint (inverseRealBrackets F i) s vr : ℝ) -
      ∑ j, (vr j : ℝ) * inverseRealRow F i j)
    ((linearPoint (inverseImaginaryBrackets F i) s vi : ℝ) -
      ∑ j, (vi j : ℝ) * inverseImaginaryRow F i j)
  have he : (1 : ℝ)/(2 : ℝ)^s + 1/(2 : ℝ)^s = 2/(2 : ℝ)^s := by ring
  have hp := ht.trans_lt (add_lt_add hr hi)
  convert hp using 1 <;> ring

def inverseRowNorm (F : FixedField K n) (i : Fin n) : ℝ :=
  ∑ j, ‖inverseFieldEmbeddingMatrix F i j‖

theorem inverse_row_perturbation (F : FixedField K n) (u v : Fin n → ℂ)
    (ε : ℝ) (hε : 0 ≤ ε) (hv : ∀ j, ‖u j-v j‖ ≤ ε) (i : Fin n) :
    ‖(inverseFieldEmbeddingMatrix F *ᵥ u) i -
      (inverseFieldEmbeddingMatrix F *ᵥ v) i‖ ≤ ε * inverseRowNorm F i := by
  have he : (inverseFieldEmbeddingMatrix F *ᵥ u) i -
      (inverseFieldEmbeddingMatrix F *ᵥ v) i =
      ∑ j, inverseFieldEmbeddingMatrix F i j * (u j-v j) := by
    simp [Matrix.mulVec,dotProduct,mul_sub,Finset.sum_sub_distrib]
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    (∑ j, ‖inverseFieldEmbeddingMatrix F i j * (u j-v j)‖) ≤
        ∑ j, ‖inverseFieldEmbeddingMatrix F i j‖ * ε := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hv j) (norm_nonneg _)
    _ = ε * inverseRowNorm F i := by
      simp [inverseRowNorm,Finset.mul_sum,mul_comm]

theorem inverseRowPoint_coordinate_error (F : FixedField K n) (s : ℕ)
    (vr vi : Fin n → ℚ) (x : K) (ε : ℝ) (hε : 0 ≤ ε)
    (hv : ∀ j, ‖rationalComplexPoint vr vi j-conjugateValues F x j‖ ≤ ε)
    (i : Fin n) :
    |(inverseRowPoint F s vr vi i : ℝ) - (F.basis.repr x i : ℝ)| <
      2/(2 : ℝ)^s + ε * inverseRowNorm F i := by
  have hm := inverse_row_perturbation F (rationalComplexPoint vr vi)
    (conjugateValues F x) ε hε hv i
  rw [inverseFieldEmbeddingMatrix_recovers] at hm
  have hre := (Complex.abs_re_le_norm _).trans hm
  simp only [Complex.sub_re,Complex.ratCast_re] at hre
  have hq := inverseRowPoint_error F s vr vi i
  have ht := abs_add_le
    ((inverseRowPoint F s vr vi i : ℝ)-
      ((inverseFieldEmbeddingMatrix F *ᵥ rationalComplexPoint vr vi) i).re)
    (((inverseFieldEmbeddingMatrix F *ᵥ rationalComplexPoint vr vi) i).re-
      (F.basis.repr x i : ℝ))
  have hp := ht.trans_lt (add_lt_add_of_lt_of_le hq hre)
  convert hp using 1 <;> ring

abbrev inverseLatticeInputEncoding (n : ℕ) :=
  pairEncoding encodingNatBool (inversePointInputEncoding n)

def inverseLatticePoint (F : FixedField K n) (D s : ℕ)
    (vr vi : Fin n → ℚ) : Fin n → ℚ :=
  fun i => latticeRound (coordinateLatticeDenominator F * D)
    (inverseRowPoint F s vr vi i)

def inverseLatticePointComputes (F : FixedField K n) :
    Computes (inverseLatticeInputEncoding n) (vectorEncoding n)
      (fun p => inverseLatticePoint F p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let D := Wiring.firstComputes encodingNatBool (inversePointInputEncoding n)
  let c := constantComputes (inverseLatticeInputEncoding n) encodingNatBool
    (coordinateLatticeDenominator F)
  let den := (pairComputes c D).andThen RationalArithmetic.naturalMultiplicationComputes
  let point := Wiring.secondComputes encodingNatBool (inversePointInputEncoding n)
  apply assembleComputes _ n _
  intro i
  exact congrComputes ((pairComputes den (point.andThen (inverseRowPointComputes F i))).andThen
    latticeRoundComputes) (fun _ => rfl)

theorem inverseLatticePoint_recovers (F : FixedField K n) (D : ℕ) (hD : 0 < D)
    (s : ℕ) (vr vi : Fin n → ℚ) (x : K) (hx : IsIntegral ℤ ((D : K)*x))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hv : ∀ j, ‖rationalComplexPoint vr vi j-conjugateValues F x j‖ ≤ ε)
    (accuracy : ∀ i, 2/(2 : ℝ)^s + ε * inverseRowNorm F i ≤
      1/(2 * (coordinateLatticeDenominator F * D : ℕ) : ℝ)) :
    inverseLatticePoint F D s vr vi = fun i => F.basis.repr x i := by
  apply rounded_coordinates_recover F D hD x hx
  intro i
  have h := (inverseRowPoint_coordinate_error F s vr vi x ε hε hv i).trans_le (accuracy i)
  apply (Rat.cast_lt (K := ℝ)).mp
  simpa only [Rat.cast_abs,Rat.cast_sub,Rat.cast_div,Rat.cast_mul,
    Rat.cast_one,Rat.cast_natCast,Rat.cast_ofNat] using h

end
end Paper2.ExactInput.FixedRootCodec
