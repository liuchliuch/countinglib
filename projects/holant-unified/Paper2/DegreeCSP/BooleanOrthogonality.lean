import Paper2.DegreeCSP.Generated
import Mathlib.Analysis.Complex.Basic

/-! Literal original-table block orthogonality and a Boolean coefficient
consequence. These definitions agree with ComplexCSP/Structure/
BlockOrthogonality.lean: complex dependence and Hermitian sums on each positive
equal-magnitude block are retained. No support-only replacement is used. -/
namespace Paper2.DegreeCSP.OriginalBO
open scoped BigOperators
noncomputable section

def Proportional {J : Type} (u v : J → ℂ) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∀ j, u j = c * v j
def support {J : Type} (u : J → ℂ) : Set J := {j | u j ≠ 0}
def MagnitudeProportional {J : Type} (u v : J → ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ j, ‖u j‖ = c * ‖v j‖
def BlockRankOne {X J : Type} (G : X → J → ℂ) : Prop :=
  ∀ x y, G x ≠ 0 → G y ≠ 0 →
    MagnitudeProportional (G x) (G y) ∨ Disjoint (support (G x)) (support (G y))
def magnitudeBlock {J : Type} [Fintype J] (u : J → ℂ) (z : J) : Finset J := by
  classical
  exact Finset.univ.filter (fun w => ‖u w‖ = ‖u z‖)
def hermitianSum {J : Type} (u v : J → ℂ) (B : Finset J) : ℂ :=
  ∑ z ∈ B, u z * star (v z)
def VectorBlockOrthogonal {J : Type} [Fintype J] (u v : J → ℂ) : Prop :=
  ∀ z, u z ≠ 0 → hermitianSum u v (magnitudeBlock u z) = 0
def BlockOrthogonal {X J : Type} [Fintype J] (G : X → J → ℂ) : Prop :=
  BlockRankOne G ∧ ∀ x y, G x ≠ 0 → G y ≠ 0 →
    MagnitudeProportional (G x) (G y) →
      Proportional (G x) (G y) ∨ VectorBlockOrthogonal (G x) (G y)

/-- Two fully occupied Boolean rows that are block-orthogonal have vanishing
actual Hermitian inner product; a singleton magnitude block cannot vanish. -/
theorem boolean_hermitian (u v : Bool → ℂ)
    (hu : ∀ j, u j ≠ 0) (hv : ∀ j, v j ≠ 0)
    (h : VectorBlockOrthogonal u v) :
    u false * star (v false) + u true * star (v true) = 0 := by
  classical
  have h0 := h false (hu false)
  by_cases he : ‖u false‖ = ‖u true‖
  · simpa [hermitianSum,magnitudeBlock,Finset.sum_filter,Fintype.sum_bool,he,add_comm]
      using h0
  · have hz : u false * star (v false) = 0 := by
      simpa [hermitianSum,magnitudeBlock,Finset.sum_filter,Fintype.sum_bool,
        he,Ne.symm he] using h0
    exact False.elim ((mul_ne_zero (hu false) (star_ne_zero.mpr (hv false))) hz)

theorem boolean_row_alternative (G : Bool → Bool → ℂ)
    (hne : ∀ i j, G i j ≠ 0) (h : BlockOrthogonal G) :
    Proportional (G false) (G true) ∨
      G false false * star (G true false) + G false true * star (G true true) = 0 := by
  have hr (i : Bool) : G i ≠ 0 := fun hz => hne i false (congrFun hz false)
  have hm : MagnitudeProportional (G false) (G true) := by
    rcases h.1 false true (hr false) (hr true) with hm | hd
    · exact hm
    · exact False.elim (Set.disjoint_left.mp hd (hne false false) (hne true false))
  rcases h.2 false true (hr false) (hr true) hm with hp | ho
  · exact Or.inl hp
  · exact Or.inr (boolean_hermitian _ _ (hne false) (hne true) ho)

/-- The original BO conditions for a full binary table and its actual square
force squared cross products to agree. This is a coefficient constraint, rather
than a claim that its support indicator describes the original table. -/
theorem binary_squared_cross (G : Bool → Bool → ℂ)
    (hne : ∀ i j, G i j ≠ 0)
    (h : BlockOrthogonal G) (h2 : BlockOrthogonal (fun i j => G i j ^ 2)) :
    (G false false * G true true) ^ 2 = (G false true * G true false) ^ 2 := by
  rcases boolean_row_alternative G hne h with ⟨c,hc,hcG⟩ | ho
  · rw [hcG false,hcG true]
    ring
  · rcases boolean_row_alternative (fun i j => G i j ^ 2)
      (fun i j => pow_ne_zero 2 (hne i j)) h2 with ⟨c,hc,hcG⟩ | ho2
    · change (∀ j, G false j ^ 2 = c * G true j ^ 2) at hcG
      calc
        _ = G false false ^ 2 * G true true ^ 2 := by ring
        _ = G false true ^ 2 * G true false ^ 2 := by
          rw [hcG false,hcG true]
          ring
        _ = _ := by ring
    · have hz : 2 * (G false false * star (G true false)) ^ 2 = 0 := by
        simp only [star_pow] at ho2
        linear_combination ho2 +
          (G false false * star (G true false) -
            G false true * star (G true true)) * ho
      have hn : (2 : ℂ) * (G false false * star (G true false)) ^ 2 ≠ 0 :=
        mul_ne_zero (by norm_num)
          (pow_ne_zero 2 (mul_ne_zero (hne false false) (star_ne_zero.mpr (hne true false))))
      exact False.elim (hn hz)

end
end Paper2.DegreeCSP.OriginalBO
