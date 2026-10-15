import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Fin

/-!
# Finite covers and their least-owner representatives

The family is indexed by occurrences, so equal sets at different indices remain
separate in the tagged union. No enumeration of the ambient type is required.
All sets and the owner test below are computable from the given finite sets.
-/

namespace Counting.Algorithm.KarpLuby

open scoped BigOperators

variable {α : Type*} [DecidableEq α] {m : ℕ}

/-- The ordinary union of an occurrence-indexed finite family. -/
def coverUnion (D : Fin m → Finset α) : Finset α :=
  Finset.univ.biUnion D

/-- The disjoint union, retaining the occurrence index of each element. -/
def tagged (D : Fin m → Finset α) : Finset (Σ _ : Fin m, α) :=
  Finset.univ.sigma D

/-- Total tagged mass, with overlap and repeated occurrences counted. -/
def mass (D : Fin m → Finset α) : ℕ :=
  ∑ i, (D i).card

/-- Number of distinct covered elements. -/
def count (D : Fin m → Finset α) : ℕ :=
  (coverUnion D).card

/-- A tagged element is its element's owner if no earlier set contains it.
Membership in the tagged union is imposed separately by `ownerEvent`. -/
def IsOwner (D : Fin m → Finset α) (p : Σ _ : Fin m, α) : Prop :=
  ∀ j, j < p.1 → p.2 ∉ D j

instance decidableIsOwner (D : Fin m → Finset α) (p : Σ _ : Fin m, α) :
    Decidable (IsOwner D p) := by
  unfold IsOwner
  infer_instance

/-- Exactly one tagged occurrence of every covered element survives. -/
def ownerEvent (D : Fin m → Finset α) : Finset (Σ _ : Fin m, α) :=
  (tagged D).filter (IsOwner D)

@[simp] theorem mem_coverUnion (D : Fin m → Finset α) (x : α) :
    x ∈ coverUnion D ↔ ∃ i, x ∈ D i := by
  simp [coverUnion]

omit [DecidableEq α] in
@[simp] theorem mem_tagged (D : Fin m → Finset α) (p : Σ _ : Fin m, α) :
    p ∈ tagged D ↔ p.2 ∈ D p.1 := by
  simp [tagged]

@[simp] theorem mem_ownerEvent (D : Fin m → Finset α) (p : Σ _ : Fin m, α) :
    p ∈ ownerEvent D ↔ p.2 ∈ D p.1 ∧ IsOwner D p := by
  simp [ownerEvent]

omit [DecidableEq α] in
@[simp] theorem card_tagged (D : Fin m → Finset α) :
    (tagged D).card = mass D := by
  simp [tagged, mass, Finset.card_sigma]

theorem subset_coverUnion (D : Fin m → Finset α) (i : Fin m) :
    D i ⊆ coverUnion D := by
  intro x hx
  exact (mem_coverUnion D x).2 ⟨i, hx⟩

theorem exists_owner (D : Fin m → Finset α) {x : α} (hx : x ∈ coverUnion D) :
    ∃ i, (⟨i, x⟩ : Σ _ : Fin m, α) ∈ ownerEvent D := by
  let s := Finset.univ.filter fun i => x ∈ D i
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := (mem_coverUnion D x).1 hx
    exact ⟨i, by simp [s, hi]⟩
  refine ⟨s.min' hs, (mem_ownerEvent D _).2 ⟨?_, ?_⟩⟩
  · simpa [s] using s.min'_mem hs
  · intro j hj hxj
    have hjmem : j ∈ s := by simp [s, hxj]
    have hmin : s.min' hs ≤ j := s.min'_le j hjmem
    exact (not_lt_of_ge hmin) hj

/-- Two valid owners of the same element have the same occurrence index. -/
theorem owner_unique (D : Fin m → Finset α)
    {p q : Σ _ : Fin m, α} (hp : p ∈ ownerEvent D) (hq : q ∈ ownerEvent D)
    (hx : p.2 = q.2) : p = q := by
  obtain ⟨hpmem, hpowner⟩ := (mem_ownerEvent D p).1 hp
  obtain ⟨hqmem, hqowner⟩ := (mem_ownerEvent D q).1 hq
  have hi : p.1 = q.1 := by
    apply le_antisymm
    · by_contra h
      exact hpowner q.1 (lt_of_not_ge h) (hx.symm ▸ hqmem)
    · by_contra h
      exact hqowner p.1 (lt_of_not_ge h) (hx ▸ hpmem)
  cases p
  cases q
  simp_all

/-- Forgetting the owner tag gives precisely the original union. -/
theorem image_ownerEvent (D : Fin m → Finset α) :
    (ownerEvent D).image (fun p => p.2) = coverUnion D := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    exact (mem_coverUnion D p.2).2 ⟨p.1, ((mem_ownerEvent D p).1 hp).1⟩
  · intro hx
    obtain ⟨i, hi⟩ := exists_owner D hx
    exact Finset.mem_image.2 ⟨⟨i, x⟩, hi, rfl⟩

/-- The key exact counting identity behind the Karp–Luby estimator. -/
@[simp] theorem card_ownerEvent (D : Fin m → Finset α) :
    (ownerEvent D).card = count D := by
  unfold count
  rw [← image_ownerEvent D]
  symm
  exact Finset.card_image_iff.2 (fun _ hp _ hq hx => owner_unique D hp hq hx)

theorem count_le_mass (D : Fin m → Finset α) : count D ≤ mass D := by
  rw [← card_ownerEvent, ← card_tagged]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Each occurrence contains at most the distinct union's cardinality. -/
theorem mass_le_mul_count (D : Fin m → Finset α) : mass D ≤ m * count D := by
  calc
    mass D ≤ ∑ _i : Fin m, count D :=
      Finset.sum_le_sum fun i _ => Finset.card_le_card (subset_coverUnion D i)
    _ = m * count D := by simp

@[simp] theorem count_eq_zero_iff (D : Fin m → Finset α) :
    count D = 0 ↔ ∀ i, D i = ∅ := by
  rw [count, Finset.card_eq_zero]
  constructor
  · intro h i
    apply Finset.eq_empty_iff_forall_notMem.2
    intro x hx
    have hmem := subset_coverUnion D i hx
    simp [h] at hmem
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.2
    intro x hx
    obtain ⟨i, hi⟩ := (mem_coverUnion D x).1 hx
    simp [h i] at hi

omit [DecidableEq α] in
@[simp] theorem mass_eq_zero_iff (D : Fin m → Finset α) :
    mass D = 0 ↔ ∀ i, D i = ∅ := by
  simp [mass]

theorem count_eq_zero_iff_mass_eq_zero (D : Fin m → Finset α) :
    count D = 0 ↔ mass D = 0 := by
  rw [count_eq_zero_iff, mass_eq_zero_iff]

theorem count_pos_iff_mass_pos (D : Fin m → Finset α) :
    0 < count D ↔ 0 < mass D := by
  simpa only [Nat.pos_iff_ne_zero, not_iff_not] using count_eq_zero_iff_mass_eq_zero D

omit [DecidableEq α] in
@[simp] theorem tagged_eq_empty_iff (D : Fin m → Finset α) :
    tagged D = ∅ ↔ ∀ i, D i = ∅ := by
  simp [tagged]

@[simp] theorem coverUnion_empty_family (D : Fin 0 → Finset α) : coverUnion D = ∅ := by
  simp [coverUnion]

omit [DecidableEq α] in
@[simp] theorem mass_empty_family (D : Fin 0 → Finset α) : mass D = 0 := by
  simp [mass]

@[simp] theorem count_empty_family (D : Fin 0 → Finset α) : count D = 0 := by
  simp [count]

end Counting.Algorithm.KarpLuby
