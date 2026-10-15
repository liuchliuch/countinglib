import Paper2.HeightOne.GroupSplit.AbstractSplit

/-! Extract a literal group generator and the exact complete subgroup formulas
from the odd dihedral presentation. -/
namespace Paper2.HeightOne.GroupSplit
open FiniteGroupFacts
noncomputable section
variable {A : Type*} [Group A]

def RotationData (J : Subgroup A) (z : A) (N : ℕ) (r : A) : Prop :=
  r ∈ J ∧ orderOf r = N ∧ z * r * z = r⁻¹ ∧
  ((J : Set A) = (Subgroup.zpowers r : Set A) ∨
    (J : Set A) = (Subgroup.zpowers r : Set A) ∪
      (fun q => z * q) '' (Subgroup.zpowers r : Set A))

theorem OddDihedralPresentation.rotation {J : Subgroup A} {z : A}
    (hz : z * z = 1) (h : OddDihedralPresentation J z) :
    ∃ N : ℕ, 3 ≤ N ∧ Odd N ∧ ∃ r : A, RotationData J z N r := by
  obtain ⟨N, hN, hodd, e, ⟨i, hzi⟩, hJ⟩ := h
  let r : A := e.symm (DihedralGroup.r 1)
  have her : e r = DihedralGroup.r 1 := e.apply_symm_apply _
  let K : Subgroup A := Subgroup.zpowers r
  have hmem (S : Subgroup A) (x : A) : x ∈ S ↔ e x ∈ S.map e.toMonoidHom := by
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      exact e.injective he ▸ hy
  have hK : K.map e.toMonoidHom = Dihedral.rotations N := by
    change (Subgroup.zpowers r).map e.toMonoidHom = _
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (e r) = _
    rw [her, ← Dihedral.rotations_eq_zpowers]
  have hk (x : A) : x ∈ K ↔ e x ∈ Dihedral.rotations N := by rw [hmem, hK]
  have hrJ : r ∈ J := by
    rw [hmem, her]
    rcases hJ with hJ | hJ <;> rw [hJ]
    · exact Dihedral.r_mem_rotations _
    · exact Subgroup.mem_top _
  have hrorder : orderOf r = N := by
    rw [← e.orderOf_eq r, her, DihedralGroup.orderOf_r_one]
  have hrel : z * r * z = r⁻¹ := by
    apply e.injective
    simp only [map_mul, map_inv, hzi, her, DihedralGroup.sr_mul_r,
      DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]
    congr 1
    abel
  refine ⟨N, hN, hodd, r, hrJ, hrorder, hrel, ?_⟩
  rcases hJ with hJ | hJ
  · left
    ext x
    exact (hmem J x).trans (hJ ▸ (hk x).symm)
  · right
    have htop (x : A) : x ∈ J := (hmem J x).mpr (hJ ▸ Subgroup.mem_top _)
    ext x
    constructor
    · intro _
      cases hex : e x with
      | r j => exact Or.inl ((hk x).mpr ⟨j, hex⟩)
      | sr j =>
        refine Or.inr ⟨z * x, (hk _).mpr ?_, ?_⟩
        · exact ⟨j - i, by simp only [map_mul, hzi, hex, DihedralGroup.sr_mul_sr]⟩
        · change z * (z * x) = x
          rw [← mul_assoc, hz, one_mul]
    · intro _
      exact htop x


lemma RotationData.map {B : Type*} [Group B] {J : Subgroup A} {z r : A} {N : ℕ}
    (h : RotationData J z N r) (f : A →* B) (hf : Function.Injective f) :
    RotationData (J.map f) (f z) N (f r) := by
  obtain ⟨hr, ho, he, hset⟩ := h
  refine ⟨⟨r, hr, rfl⟩, (orderOf_injective f hf r).trans ho, ?_, ?_⟩
  · simpa only [map_mul, map_inv] using congrArg f he
  · have hzpow : f '' (Subgroup.zpowers r : Set A) = (Subgroup.zpowers (f r) : Set B) :=
      congrArg (fun H : Subgroup B => (H : Set B)) (f.map_zpowers r)
    have hcoset : f '' ((fun q => z * q) '' (Subgroup.zpowers r : Set A)) =
        (fun q => f z * q) '' (Subgroup.zpowers (f r) : Set B) := by
      rw [← hzpow, Set.image_image, Set.image_image]
      congr 1
      funext q
      exact map_mul f z q
    rcases hset with hset | hset
    · left
      change f '' (J : Set A) = _
      rw [hset, hzpow]
    · right
      change f '' (J : Set A) = _
      rw [hset, Set.image_union, hzpow, hcoset]

end
end Paper2.HeightOne.GroupSplit
