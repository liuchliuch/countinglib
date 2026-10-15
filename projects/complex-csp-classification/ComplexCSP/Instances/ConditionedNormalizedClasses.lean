import ComplexCSP.Instances.ConditionedRowMoments
import Mathlib.Data.Real.Sqrt

/-! # Exact identification of normalized twins with proportional-row classes

The finite sums retain all members of each class. Positive diagonals and actual
symmetry are used; no equality of distinct colors or class cardinalities is
assumed. This is the algebraic bridge to a normalization-moment hardness theorem.
-/
namespace ComplexCSP.ConditionedRowMoments
open RowTypes
open scoped BigOperators

variable {R : Type}

noncomputable def normalized (A : R → R → ℝ) (i j : R) : ℝ :=
  A i j / (Real.sqrt (A i i) * Real.sqrt (A j j))

theorem normalized_recover (A : R → R → ℝ) (hd : ∀ i, 0 < A i i) (i j : R) :
    A i j = (Real.sqrt (A i i) * Real.sqrt (A j j)) * normalized A i j := by
  exact (mul_div_cancel₀ _ (mul_ne_zero (Real.sqrt_pos.mpr (hd i)).ne'
    (Real.sqrt_pos.mpr (hd j)).ne')).symm

/-- Normalized row equality has a concrete nonzero scalar in the original rows. -/
theorem proportional_of_normalized_eq (A : R → R → ℝ) (hd : ∀ i, 0 < A i i)
    (i j : R) (he : normalized A i = normalized A j) : Proportional (A i) (A j) := by
  have hi : Real.sqrt (A i i) ≠ 0 := (Real.sqrt_pos.mpr (hd i)).ne'
  have hj : Real.sqrt (A j j) ≠ 0 := (Real.sqrt_pos.mpr (hd j)).ne'
  refine ⟨Real.sqrt (A i i) / Real.sqrt (A j j), div_ne_zero hi hj, ?_⟩
  intro k
  rw [normalized_recover A hd i k,congrFun he k,normalized_recover A hd j k]
  field_simp

/-- Positivity forces the proportionality scalar positive and fixes the exact
square-root diagonal factor, so normalization removes it. -/
theorem normalized_eq_of_proportional (A : R → R → ℝ)
    (hA : ∀ i j, 0 < A i j) (hs : ∀ i j, A i j = A j i)
    (i j : R) (he : Proportional (A i) (A j)) : normalized A i = normalized A j := by
  obtain ⟨c,hc,hrow⟩ := he
  have hcp : 0 < c := by
    have hh := hA i j
    rw [hrow j] at hh
    exact (mul_pos_iff_of_pos_right (hA j j)).mp hh
  have hii : A i i = c^2 * A j j := by
    calc
      _ = c * A j i := hrow i
      _ = c * A i j := by rw [hs j i]
      _ = c * (c * A j j) := by rw [hrow j]
      _ = _ := by ring
  have hsqrt : Real.sqrt (A i i) = c * Real.sqrt (A j j) := by
    rw [hii,Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq_eq_abs,abs_of_pos hcp]
  funext k
  simp only [normalized,hrow k,hsqrt]
  field_simp [hc]

 theorem normalized_eq_iff_proportional (A : R → R → ℝ)
    (hA : ∀ i j, 0 < A i j) (hs : ∀ i j, A i j = A j i) (i j : R) :
    normalized A i = normalized A j ↔ Proportional (A i) (A j) :=
  ⟨proportional_of_normalized_eq A (fun i => hA i i) i j,
    normalized_eq_of_proportional A hA hs i j⟩

variable [Fintype R]

noncomputable def normalizedClassWeight (A : R → R → ℝ) (w : R → ℝ) (x : R) : ℝ := by
  classical
  exact ∑ i, if normalized A i = normalized A x then w i else 0

/-- Equality of the literal finite sums, including all original class weights. -/
theorem normalizedClassWeight_eq (A : R → R → ℝ)
    (hA : ∀ i j, 0 < A i j) (hs : ∀ i j, A i j = A j i) (w : R → ℝ) (x : R) :
    normalizedClassWeight A w x = classWeight A w x := by
  classical
  simp only [normalizedClassWeight,classWeight,normalized_eq_iff_proportional A hA hs]

end ComplexCSP.ConditionedRowMoments
