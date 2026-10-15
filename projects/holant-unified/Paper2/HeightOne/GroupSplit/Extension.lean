import Paper2.HeightOne.GroupSplit.PGL
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

/-! The actual two-coset extension by the distinguished involution. -/
namespace Paper2.HeightOne.GroupSplit
variable {A : Type*} [Group A]

/-- An involution normalizing the complete subgroup gives exactly two possible
cosets. This construction does not enumerate or replace the original subgroup. -/
def involutionExtension (G : Subgroup A) (z : A) (hz : z * z = 1)
    (hnorm : ∀ g ∈ G, z * g * z ∈ G) : Subgroup A where
  carrier := {x | x ∈ G ∨ z * x ∈ G}
  one_mem' := Or.inl G.one_mem
  mul_mem' := by
    intro x y hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (G.mul_mem hx hy)
    · right
      have h := G.mul_mem (hnorm x hx) hy
      simpa only [mul_assoc, ← mul_assoc z z y, hz, one_mul] using h
    · exact Or.inr (by simpa only [mul_assoc] using G.mul_mem hx hy)
    · left
      have h := G.mul_mem (hnorm (z * x) hx) hy
      have he : z * (z * x) * z * (z * y) = x * y := by
        calc
          _ = (z * z) * x * (z * z) * y := by group
          _ = _ := by rw [hz]; simp
      exact he ▸ h
  inv_mem' := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (G.inv_mem hx)
    · right
      have hzInv : z⁻¹ = z := inv_eq_of_mul_eq_one_left hz
      have h := hnorm _ (G.inv_mem hx)
      simpa only [mul_inv_rev, hzInv, mul_assoc, hz, mul_one] using h

lemma le_involutionExtension (G : Subgroup A) (z : A) (hz : z * z = 1)
    (hnorm : ∀ g ∈ G, z * g * z ∈ G) : G ≤ involutionExtension G z hz hnorm :=
  fun _ h => Or.inl h

lemma involution_mem_extension (G : Subgroup A) (z : A) (hz : z * z = 1)
    (hnorm : ∀ g ∈ G, z * g * z ∈ G) : z ∈ involutionExtension G z hz hnorm :=
  Or.inr (hz ▸ G.one_mem)

lemma extension_carrier (G : Subgroup A) (z : A) (hz : z * z = 1)
    (hnorm : ∀ g ∈ G, z * g * z ∈ G) :
    (involutionExtension G z hz hnorm : Set A) = (G : Set A) ∪ (fun g => z * g) '' G := by
  ext x
  change (x ∈ G ∨ z * x ∈ G) ↔ x ∈ G ∨ ∃ g ∈ G, z * g = x
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨z * x, h, by rw [← mul_assoc, hz, one_mul]⟩
  · rintro (h | ⟨g, hg, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by simpa only [← mul_assoc, hz, one_mul] using hg)

lemma extension_finite (G : Subgroup A) (z : A) (hz : z * z = 1)
    (hnorm : ∀ g ∈ G, z * g * z ∈ G) (hG : (G : Set A).Finite) :
    (involutionExtension G z hz hnorm : Set A).Finite := by
  rw [extension_carrier]
  exact hG.union (hG.image _)

lemma extension_eq_of_mem (G : Subgroup A) (z : A) (hz : z * z = 1)
    (hnorm : ∀ g ∈ G, z * g * z ∈ G) (hzG : z ∈ G) :
    involutionExtension G z hz hnorm = G := by
  apply le_antisymm _ (le_involutionExtension G z hz hnorm)
  intro x hx
  rcases hx with hx | hx
  · exact hx
  · have h := G.mul_mem hzG hx
    simpa only [← mul_assoc, hz, one_mul] using h

lemma extension_index_two (G : Subgroup A) (z : A) (hz : z * z = 1)
    (hnorm : ∀ g ∈ G, z * g * z ∈ G) (hzG : z ∉ G) :
    (G.subgroupOf (involutionExtension G z hz hnorm)).index = 2 := by
  apply Subgroup.index_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨⟨z, involution_mem_extension G z hz hnorm⟩, hzG, ?_⟩
  intro x
  exact x.property.symm

end Paper2.HeightOne.GroupSplit
