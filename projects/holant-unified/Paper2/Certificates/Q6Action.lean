import Paper2.Certificates.Q6CoverageBridge
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.IntervalCases

/-! The orbit action is the actual relabeling/global complementation of port
subsets. This identifies the numerical mask witness with coordinate semantics. -/
namespace Paper2.Certificates.Q6

open Coverage

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem testBit_mask (S : PortSet) (v : Port) :
    (mask S).testBit v.val = decide (v ∈ S) := by
  revert S v
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem xor_mask (S : PortSet) :
    (mask S) ^^^ 63 = mask (Finset.univ \ S) := by
  revert S
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tripleSet_complement (i : Fin 20) :
    tripleSet (complementCoord i) = Finset.univ \ tripleSet i := by
  revert i
  decide +kernel

theorem permuteMask_mask (p : Equiv.Perm Port) (S : PortSet) :
    permuteMask p (mask S) = mask (S.image p) := by
  unfold permuteMask
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  simp only [testBit_mask, decide_eq_true_eq]
  rw [mask, Finset.sum_image (fun a _ b _ hab => p.injective hab)]
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The actual action on a set of occupied ports. -/
def actSet (p : Equiv.Perm Port) (c : Bool) (S : PortSet) : PortSet :=
  if c then Finset.univ \ S.image p else S.image p

theorem actedMask_mask (p : Equiv.Perm Port) (c : Bool) (S : PortSet) :
    actedMask p c (mask S) = mask (actSet p c S) := by
  cases c
  · exact permuteMask_mask p S
  · change (permuteMask p (mask S)) ^^^ 63 = _
    rw [permuteMask_mask, xor_mask]
    rfl

theorem image_univ_perm (p : Equiv.Perm Port) : Finset.univ.image p = Finset.univ := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  exact ⟨p.symm v,p.apply_symm_apply v⟩

theorem actSet_complement (p : Equiv.Perm Port) (c : Bool) (S : PortSet) :
    actSet p c (Finset.univ \ S) = Finset.univ \ actSet p c S := by
  cases c <;> simp only [actSet, Bool.false_eq_true, ↓reduceIte,
    Finset.image_sdiff _ _ p.injective, image_univ_perm]

noncomputable def Coverage.Action.portEquiv (a : Action) (ha : a.Valid) : Equiv.Perm Port :=
  Equiv.ofBijective a.ports ha.1

theorem coordinateMasks_eq : coordinateMasks = tripleMasks := rfl

theorem Coverage.Action.tripleSet_eq (a : Action) (ha : a.Valid) (i : Fin 20) :
    tripleSet (a.coords i) = actSet (a.portEquiv ha) a.complement (tripleSet i) := by
  apply mask_injective
  rw [(tripleSet_correct (a.coords i)).2]
  have h := ha.2.2 i
  rw [coordinateMasks_eq] at h
  rw [h, ← (tripleSet_correct i).2]
  exact actedMask_mask (a.portEquiv ha) a.complement (tripleSet i)

theorem Coverage.Action.complement_commutes (a : Action) (ha : a.Valid) (i : Fin 20) :
    a.coords (complementCoord i) = complementCoord (a.coords i) := by
  apply tripleMasks_injective
  rw [← (tripleSet_correct _).2, ← (tripleSet_correct _).2]
  congr 1
  rw [a.tripleSet_eq ha, tripleSet_complement, actSet_complement,
    tripleSet_complement, a.tripleSet_eq ha]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask_lt_64 (S : PortSet) : mask S < 64 := by
  revert S
  decide +kernel

theorem card_three_of_mask_eq (S : PortSet) (i : Fin 20)
    (h : mask S = tripleMasks i) : S.card = 3 := by
  have hs : S = tripleSet i := mask_injective (h.trans (tripleSet_correct i).2.symm)
  rw [hs]
  exact (tripleSet_correct i).1

theorem actSet_card_three_iff (p : Equiv.Perm Port) (c : Bool) (S : PortSet) :
    (actSet p c S).card = 3 ↔ S.card = 3 := by
  have him : (S.image p).card = S.card := Finset.card_image_iff.mpr p.injective.injOn
  cases c
  · exact him ▸ Iff.rfl
  · change (Finset.univ \ S.image p).card = 3 ↔ S.card = 3
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),him]
    have hbound : S.card ≤ 6 := (Finset.card_le_card (Finset.subset_univ S))
    change 6 - S.card = 3 ↔ S.card = 3
    omega

variable {K : Type*} [Zero K]

/-- The mask encoding vanishes exactly outside its designated triple layer. -/
theorem coefficient_mask_zero (q : Fin 20 → K) (S : PortSet) (hS : S.card ≠ 3) :
    coefficient q (mask S) = 0 := by
  have hm := mask_lt_64 S
  generalize he : mask S = m at *
  interval_cases m
  all_goals first
    | rfl
    | exact False.elim (hS (card_three_of_mask_eq S 0 he))
    | exact False.elim (hS (card_three_of_mask_eq S 1 he))
    | exact False.elim (hS (card_three_of_mask_eq S 2 he))
    | exact False.elim (hS (card_three_of_mask_eq S 3 he))
    | exact False.elim (hS (card_three_of_mask_eq S 4 he))
    | exact False.elim (hS (card_three_of_mask_eq S 5 he))
    | exact False.elim (hS (card_three_of_mask_eq S 6 he))
    | exact False.elim (hS (card_three_of_mask_eq S 7 he))
    | exact False.elim (hS (card_three_of_mask_eq S 8 he))
    | exact False.elim (hS (card_three_of_mask_eq S 9 he))
    | exact False.elim (hS (card_three_of_mask_eq S 10 he))
    | exact False.elim (hS (card_three_of_mask_eq S 11 he))
    | exact False.elim (hS (card_three_of_mask_eq S 12 he))
    | exact False.elim (hS (card_three_of_mask_eq S 13 he))
    | exact False.elim (hS (card_three_of_mask_eq S 14 he))
    | exact False.elim (hS (card_three_of_mask_eq S 15 he))
    | exact False.elim (hS (card_three_of_mask_eq S 16 he))
    | exact False.elim (hS (card_three_of_mask_eq S 17 he))
    | exact False.elim (hS (card_three_of_mask_eq S 18 he))
    | exact False.elim (hS (card_three_of_mask_eq S 19 he))

/-- Exact coefficient pullback on the triple layer, for card/loop naturality. -/
theorem coefficient_action_on_subset (q : Fin 20 → K) (a : Action) (ha : a.Valid)
    (S : PortSet) (hS : S.card = 3) :
    coefficient (fun i => q (a.coords i)) (mask S) =
      coefficient q (mask (actSet (a.portEquiv ha) a.complement S)) := by
  obtain ⟨i,hi⟩ := tripleMasks_complete S hS
  have hSi : S = tripleSet i := mask_injective (hi.trans (tripleSet_correct i).2.symm)
  subst S
  rw [(tripleSet_correct i).2,coefficient_at_triple]
  rw [← a.tripleSet_eq ha i,(tripleSet_correct (a.coords i)).2,coefficient_at_triple]


/-- Coefficient naturality also holds off the triple layer; neither endpoint
term nor a subset-cardinality side condition is hidden in this statement. -/
theorem coefficient_action (q : Fin 20 → K) (a : Action) (ha : a.Valid)
    (S : PortSet) :
    coefficient (fun i => q (a.coords i)) (mask S) =
      coefficient q (mask (actSet (a.portEquiv ha) a.complement S)) := by
  by_cases hS : S.card = 3
  · exact coefficient_action_on_subset q a ha S hS
  · rw [coefficient_mask_zero _ S hS,
      coefficient_mask_zero _ _ (fun h => hS ((actSet_card_three_iff _ _ S).mp h))]

/-- Support on a complementary pair survives every verified orbit action. -/
theorem OneComplementPair.of_action (q : Fin 20 → K) (a : Action) (ha : a.Valid)
    (h : OneComplementPair (fun i => q (a.coords i))) : OneComplementPair q := by
  obtain ⟨i,hi⟩ := h
  refine ⟨a.coords i, ?_⟩
  intro j hj
  obtain ⟨k,rfl⟩ := ha.2.1.2 j
  rcases hi k hj with hk | hk
  · exact Or.inl (congrArg a.coords hk)
  · exact Or.inr ((congrArg a.coords hk).trans (a.complement_commutes ha i))

end Paper2.Certificates.Q6
