import ComplexCSP.Structure.BlockOrthogonality
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # The strict Gram obstruction in Cai–Chen's non-block-rank-one reduction

This is finite real algebra, including the equality case of Cauchy–Schwarz.
No graph-homomorphism dichotomy or complexity assumption occurs here.
-/
namespace ComplexCSP.GramObstruction
open scoped BigOperators

variable {X D : Type} [Fintype D]

def gram (A : X → D → ℝ) (x y : X) : ℝ := ∑ z, A x z * A y z

@[simp] theorem gram_symm (A : X → D → ℝ) (x y : X) :
    gram A x y = gram A y x := by
  unfold gram
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem gram_nonneg (A : X → D → ℝ) (hA : ∀ x z, 0 ≤ A x z) (x y : X) :
    0 ≤ gram A x y := Finset.sum_nonneg fun z _ => mul_nonneg (hA x z) (hA y z)

theorem gram_pos_of_common (A : X → D → ℝ) (hA : ∀ x z, 0 ≤ A x z)
    (x y : X) (z : D) (hx : 0 < A x z) (hy : 0 < A y z) : 0 < gram A x y := by
  exact (mul_pos hx hy).trans_le
    (Finset.single_le_sum (fun w _ => mul_nonneg (hA x w) (hA y w)) (Finset.mem_univ z))

/-- Twice the Gram determinant is the sum of squares of all ordered minors. -/
theorem lagrange_identity (u v : D → ℝ) :
    2 * ((∑ z, u z * u z) * (∑ z, v z * v z) - (∑ z, u z * v z)^2) =
      ∑ i, ∑ j, (u i * v j - u j * v i)^2 := by
  simp_rw [sub_sq, mul_pow]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  have h (i : D) : ∑ j, 2 * (u i * v j) * (u j * v i) =
      (2 * (u i * v i)) * ∑ j, u j * v j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [h, ← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [pow_two]
  ring

/-- The equality case is proved from the actual finite sum of squared minors. -/
theorem strict_cauchy_of_minor (u v : D → ℝ) (i j : D)
    (hij : u i * v j ≠ u j * v i) :
    (∑ z, u z * v z)^2 < (∑ z, u z * u z) * (∑ z, v z * v z) := by
  have hterm : 0 < (u i * v j - u j * v i)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hij)
  have hrow : (u i * v j - u j * v i)^2 ≤
      ∑ j, (u i * v j - u j * v i)^2 :=
    Finset.single_le_sum (f := fun j => (u i * v j - u j * v i)^2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have hall : (∑ j, (u i * v j - u j * v i)^2) ≤
      ∑ i, ∑ j, (u i * v j - u j * v i)^2 :=
    Finset.single_le_sum (f := fun i => ∑ j, (u i * v j - u j * v i)^2)
      (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg _))
      (Finset.mem_univ i)
  have := hterm.trans_le (hrow.trans hall)
  rw [← lagrange_identity u v] at this
  linarith

omit [Fintype D] in
/-- With a positive shared coordinate, vanishing minors force positive
proportionality, with the scalar explicitly given by that coordinate ratio. -/
theorem proportional_of_minors (u v : D → ℝ) (z : D)
    (hu : 0 < u z) (hv : 0 < v z)
    (h : ∀ i, u i * v z = u z * v i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, u i = c * v i := by
  refine ⟨u z / v z, div_pos hu hv, ?_⟩
  intro i
  apply (mul_right_cancel₀ (ne_of_gt hv))
  rw [h i]
  field_simp

/-- A non-proportional overlapping pair produces the strict positive Gram minor
used in Cai–Chen, Lemmas 3 and 4. -/
theorem pair_obstruction (A : X → D → ℝ) (hA : ∀ x z, 0 ≤ A x z)
    (x y : X) (z : D) (hx : 0 < A x z) (hy : 0 < A y z)
    (hp : ¬∃ c : ℝ, 0 < c ∧ ∀ i, A x i = c * A y i) :
    0 < gram A x x ∧ 0 < gram A x y ∧ 0 < gram A y y ∧
      gram A x y * gram A y x < gram A x x * gram A y y := by
  have hm : ∃ i, A x i * A y z ≠ A x z * A y i := by
    by_contra h
    push_neg at h
    exact hp (proportional_of_minors (A x) (A y) z hx hy h)
  obtain ⟨i, hi⟩ := hm
  refine ⟨gram_pos_of_common A hA x x z hx hx,
    gram_pos_of_common A hA x y z hx hy,
    gram_pos_of_common A hA y y z hy hy, ?_⟩
  rw [gram_symm A y x, ← pow_two]
  exact strict_cauchy_of_minor (A x) (A y) i z hi

/-- Literal complex block-rank failure supplies the required real Gram witness. -/
theorem complex_obstruction (G : X → D → ℂ)
    (h : ¬BlockOrthogonality.BlockRankOne G) :
    ∃ x y, 0 < gram (fun x z => ‖G x z‖) x x ∧
      0 < gram (fun x z => ‖G x z‖) x y ∧
      0 < gram (fun x z => ‖G x z‖) y y ∧
      gram (fun x z => ‖G x z‖) x y * gram (fun x z => ‖G x z‖) y x <
        gram (fun x z => ‖G x z‖) x x * gram (fun x z => ‖G x z‖) y y := by
  classical
  unfold BlockOrthogonality.BlockRankOne at h
  push_neg at h
  obtain ⟨x, y, hx, hy, hp, hd⟩ := h
  obtain ⟨z, hxz, hyz⟩ := Set.not_disjoint_iff.mp hd
  exact ⟨x, y, pair_obstruction _ (fun _ _ => norm_nonneg _) x y z
    (norm_pos_iff.mpr hxz) (norm_pos_iff.mpr hyz) hp⟩

/-- The produced real Gram matrix itself violates the literal complex
block-rank-one definition after the canonical real embedding. -/
theorem gram_not_blockRankOne (G : X → D → ℂ)
    (h : ¬BlockOrthogonality.BlockRankOne G) :
    ¬BlockOrthogonality.BlockRankOne
      (fun x y => (gram (fun x z => ‖G x z‖) x y : ℂ)) := by
  obtain ⟨x,y,hxx,hxy,hyy,hdet⟩ := complex_obstruction G h
  let A := gram (fun x z => ‖G x z‖)
  have hnn : ∀ x y, 0 ≤ A x y := gram_nonneg _ (fun _ _ => norm_nonneg _)
  have hyx : 0 < A y x := by simpa only [A,gram_symm] using hxy
  intro hb
  change BlockOrthogonality.BlockRankOne (fun x y => (A x y : ℂ)) at hb
  have hxn : (fun z => (A x z : ℂ)) ≠ 0 := by
    intro hz
    have he : (A x x : ℂ) = 0 := congrFun hz x
    have this : A x x = 0 := Complex.ofReal_eq_zero.mp he
    exact (ne_of_gt hxx) (by exact_mod_cast this)
  have hyn : (fun z => (A y z : ℂ)) ≠ 0 := by
    intro hz
    have he : (A y y : ℂ) = 0 := congrFun hz y
    have this : A y y = 0 := Complex.ofReal_eq_zero.mp he
    exact (ne_of_gt hyy) (by exact_mod_cast this)
  rcases hb x y hxn hyn with ⟨c,hc,hp⟩ | hd
  · have hx : ‖(A x x : ℂ)‖ = c * ‖(A y x : ℂ)‖ := hp x
    have hy : ‖(A x y : ℂ)‖ = c * ‖(A y y : ℂ)‖ := hp y
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hnn _ _)] at hx hy
    change A x y * A y x < A x x * A y y at hdet
    rw [hx,hy] at hdet
    nlinarith
  · apply Set.disjoint_left.mp hd (show (A x x : ℂ) ≠ 0 by exact_mod_cast ne_of_gt hxx)
    change (A y x : ℂ) ≠ 0
    exact_mod_cast ne_of_gt hyx

end ComplexCSP.GramObstruction
