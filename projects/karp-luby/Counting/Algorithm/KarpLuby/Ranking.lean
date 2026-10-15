import Counting.Algorithm.KarpLuby.FiniteCover
import Mathlib.Data.Fintype.EquivFin

/-!
# Ranked covers and padding

The finite-cover analysis is invariant under any bijective enumeration of the
tagged set. A concrete frontend must supply its own rank/unrank equivalence;
the existence-only enumeration below is for the mathematical API.
-/
namespace Counting.Algorithm.KarpLuby

variable {α : Type*} [DecidableEq α] {m : ℕ}

/-- A ranking for proof-level finite sets; executable frontends supply their own. -/
noncomputable def canonicalRanking (D : Fin m → Finset α) :
    {p // p ∈ tagged D} ≃ Fin (mass D) :=
  Fintype.equivFinOfCardEq (by simp)

/-- Owner codes embed into every padding space large enough for all tags. -/
def ownerCodeEmbedding (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D))
    {q : ℕ} (hq : mass D ≤ q) : {p // p ∈ ownerEvent D} ↪ Fin q where
  toFun p := Fin.castLE hq (e ⟨p.val, (Finset.mem_filter.mp p.property).1⟩)
  inj' := by
    intro p p' h
    have he : e ⟨p.val, (Finset.mem_filter.mp p.property).1⟩ =
        e ⟨p'.val, (Finset.mem_filter.mp p'.property).1⟩ := by
      apply Fin.ext
      exact congrArg (fun z : Fin q => z.val) h
    have hp := congrArg Subtype.val (e.injective he)
    exact Subtype.ext hp

/-- The successful integer codes after padding. -/
def paddedOwnerCodes (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D))
    {q : ℕ} (hq : mass D ≤ q) : Finset (Fin q) :=
  Finset.univ.map (ownerCodeEmbedding D e hq)

@[simp] theorem card_paddedOwnerCodes (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D))
    {q : ℕ} (hq : mass D ≤ q) : (paddedOwnerCodes D e hq).card = count D := by
  simp [paddedOwnerCodes]

/-- Prefix/unrank implementations can use this membership specification. -/
theorem mem_paddedOwnerCodes (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D))
    {q : ℕ} (hq : mass D ≤ q) (r : Fin q) :
    r ∈ paddedOwnerCodes D e hq ↔
      ∃ h : r.val < mass D, IsOwner D (e.symm ⟨r.val, h⟩).val := by
  constructor
  · intro hr
    obtain ⟨p, _, hp⟩ := Finset.mem_map.mp hr
    have hv : (e ⟨p.val, (Finset.mem_filter.mp p.property).1⟩).val = r.val :=
      congrArg Fin.val hp
    have hlt : r.val < mass D := hv ▸ (e ⟨p.val, (Finset.mem_filter.mp p.property).1⟩).isLt
    refine ⟨hlt, ?_⟩
    have he : (⟨r.val, hlt⟩ : Fin (mass D)) =
        e ⟨p.val, (Finset.mem_filter.mp p.property).1⟩ := Fin.ext hv.symm
    rw [he, e.symm_apply_apply]
    exact (Finset.mem_filter.mp p.property).2
  · rintro ⟨h, howner⟩
    let p := e.symm (⟨r.val, h⟩ : Fin (mass D))
    have hp : p.val ∈ ownerEvent D := Finset.mem_filter.mpr ⟨p.property, howner⟩
    refine Finset.mem_map.mpr ⟨⟨p.val, hp⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change (e p).val = r.val
    simp [p]

/-- Padding codes outside the true tagged mass always fail. -/
theorem not_mem_paddedOwnerCodes_of_mass_le (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D))
    {q : ℕ} (hq : mass D ≤ q) (r : Fin q) (hr : mass D ≤ r.val) :
    r ∉ paddedOwnerCodes D e hq := by
  rw [mem_paddedOwnerCodes]
  rintro ⟨h, _⟩
  omega

end Counting.Algorithm.KarpLuby
