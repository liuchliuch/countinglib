import ComplexCSP.Structure.RowTypes
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # A genuine arbitrary-color conditioning obstruction

No pair of colors is removed. Each conditioned matrix retains every original
color and every proportional-row-class multiplicity. If both endpoint-column
conditionings had balanced diagonal class sums, a strict positive principal
minor would be impossible.
-/
namespace ComplexCSP.ConditionedRowMoments
open RowTypes
open scoped BigOperators

variable {R : Type}

noncomputable def condition (A : R → R → ℝ) (z : R) (i j : R) : ℝ :=
  A i j * A i z * A j z

theorem condition_positive (A : R → R → ℝ) (hA : ∀ i j, 0 < A i j) (z : R) :
    ∀ i j, 0 < condition A z i j := by
  intro i j
  exact mul_pos (mul_pos (hA i j) (hA i z)) (hA j z)

theorem proportional_condition_iff (A : R → R → ℝ) (z : R)
    (hz : ∀ i, A i z ≠ 0) (i j : R) :
    Proportional (condition A z i) (condition A z j) ↔ Proportional (A i) (A j) := by
  constructor
  · rintro ⟨c,hc,hrow⟩
    refine ⟨c * A j z / A i z,div_ne_zero (mul_ne_zero hc (hz j)) (hz i),?_⟩
    intro k
    apply mul_right_cancel₀ (hz i)
    apply mul_right_cancel₀ (hz k)
    calc
      (A i k * A i z) * A k z = condition A z i k := rfl
      _ = c * condition A z j k := hrow k
      _ = ((c * A j z / A i z * A j k) * A i z) * A k z := by
        dsimp [condition]
        field_simp [hz i]
  · rintro ⟨c,hc,hrow⟩
    refine ⟨c * A i z / A j z,div_ne_zero (mul_ne_zero hc (hz i)) (hz j),?_⟩
    intro k
    dsimp [condition]
    rw [hrow k]
    field_simp [hz j]

variable [Fintype R]

/-- This finite sum retains every member of the actual proportional-row class. -/
noncomputable def classWeight (A : R → R → ℝ) (w : R → ℝ) (x : R) : ℝ := by
  classical
  exact ∑ i, if Proportional (A i) (A x) then w i else 0

/-- The diagonal first-moment invariant supplied by a planar non-hardness
normalization theorem. It is a transparent matrix property, not hardness. -/
def Balanced (A : R → R → ℝ) : Prop :=
  ∀ x y, classWeight A (fun i => A i i) x = classWeight A (fun i => A i i) y

theorem classWeight_condition (A : R → R → ℝ) (z : R)
    (hz : ∀ i, A i z ≠ 0) (w : R → ℝ) (x : R) :
    classWeight (condition A z) w x = classWeight A w x := by
  classical
  simp only [classWeight,proportional_condition_iff A z hz]

theorem classWeight_pos (A : R → R → ℝ) (w : R → ℝ) (hw : ∀ i, 0 < w i) (x : R) :
    0 < classWeight A w x := by
  classical
  unfold classWeight
  apply Finset.sum_pos'
  · intro i _
    split_ifs
    · exact (hw i).le
    · exact le_rfl
  · refine ⟨x,Finset.mem_univ x,?_⟩
    rw [if_pos (proportional_refl (A x))]
    exact hw x

/-- The exact cross-moment equation on one proportional-row class. -/
theorem classMoment_relation (A : R → R → ℝ) (x y : R) :
    A x x ^ 2 * classWeight A (fun i => condition A y i i) x =
      A x y ^ 2 * classWeight A (fun i => condition A x i i) x := by
  classical
  unfold classWeight
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Proportional (A i) (A x)
  · simp only [if_pos hi,condition]
    obtain ⟨c,_,hrow⟩ := hi
    rw [hrow x,hrow y]
    ring
  · simp [hi]

/-- At least one actual column conditioning violates the first-moment
invariant. No arbitrary-color restriction or singleton indicator is assumed. -/
theorem not_both_balanced (A : R → R → ℝ) (hA : ∀ i j, 0 < A i j)
    (hs : ∀ i j, A i j = A j i) (x y : R)
    (hminor : A x y ^ 2 < A x x * A y y) :
    ¬ (Balanced (condition A x) ∧ Balanced (condition A y)) := by
  rintro ⟨hx,hy⟩
  have bx := hx x y
  have by' := hy x y
  rw [classWeight_condition A x (fun i => (hA i x).ne'),
    classWeight_condition A x (fun i => (hA i x).ne')] at bx
  rw [classWeight_condition A y (fun i => (hA i y).ne'),
    classWeight_condition A y (fun i => (hA i y).ne')] at by'
  have h1 := classMoment_relation A x y
  have h2 := classMoment_relation A y x
  rw [by'] at h1
  rw [← bx,hs y x] at h2
  let S := classWeight A (fun i => condition A x i i) x
  let T := classWeight A (fun i => condition A y i i) y
  have hS : 0 < S := classWeight_pos A _ (fun i => condition_positive A hA x i i) x
  have he : (A x x * A y y)^2 * S = (A x y^2)^2 * S := by
    calc
      _ = A x x^2 * (A y y^2 * S) := by ring
      _ = A x x^2 * (A x y^2 * T) := by rw [h2]
      _ = A x y^2 * (A x x^2 * T) := by ring
      _ = A x y^2 * (A x y^2 * S) := by rw [h1]
      _ = _ := by ring
  have heq := mul_right_cancel₀ hS.ne' he
  have hnon : 0 ≤ A x x * A y y := mul_nonneg (hA x x).le (hA y y).le
  have hf := (sq_eq_sq₀ hnon (sq_nonneg (A x y))).mp heq
  exact (ne_of_gt hminor) hf

end ComplexCSP.ConditionedRowMoments
