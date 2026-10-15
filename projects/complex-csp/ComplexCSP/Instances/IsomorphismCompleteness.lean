import ComplexCSP.Instances.PinnedExtension
import ComplexCSP.Instances.IsomorphismTwins

/-! # All-instance isomorphism and prescribed pin twins

The strengthened all-instance premise yields the full equivalence, including
twin multiplicities. See docs/paper.md for the correction to printed Theorem 5.2. -/

set_option backward.isDefEq.respectTransparency false

namespace ComplexCSP

namespace Instance

variable {A B K ι V H : Type} {L : Language A K ι}

/-- Reinterpreting a literal instance back in its original tables restores the
same instance, including every scope occurrence and multiplicity. -/
@[simp] theorem retarget_back (I : Instance L V H)
    (g : (i : ι) → (Fin (L.arity i) → B) → K) :
    (I.retarget g).retarget L.value = I := by
  cases I with
  | mk cs =>
    simp only [retarget, List.map_map]
    change Instance.mk (cs.map id) = Instance.mk cs
    rw [List.map_id]

end Instance

namespace PinnedIsomorphism

variable {A B K ι V : Type} [Field K] [CharZero K]
variable [Fintype A] [Fintype B]
variable (L : Language A K ι)
variable (g : (i : ι) → (Fin (L.arity i) → B) → K)

omit [CharZero K] in
/-- Universal equality is symmetric under literal retargeting of every template. -/
theorem AllPinnedEqual.symm {a : V → A} {b : V → B}
    (h : AllPinnedEqual L g a b) : AllPinnedEqual (L.retarget g) L.value b a := by
  intro H hH dH I
  have he := h H (I.retarget L.value)
  have hb : (I.retarget L.value).retarget g = I := Instance.retarget_back I L.value
  rw [hb] at he
  exact he.symm

/-- Two applications of exact pin extension produce matching tuples which
simultaneously enumerate both target domains. Original pins are preserved as
the leftmost summand, rather than replaced or identified. -/
theorem exists_both_surjective_extension (a : V → A) (b : V → B)
    (h : AllPinnedEqual L g a b) :
    ∃ y : A → B, ∃ x : B → A,
      AllPinnedEqual L g (Sum.elim (Sum.elim a id) x)
        (Sum.elim (Sum.elim b y) id) := by
  classical
  obtain ⟨y, hy⟩ := exists_pinned_extension L g a b h (id : A → A)
  obtain ⟨x, hx⟩ := exists_pinned_extension (L.retarget g) L.value
    (Sum.elim b y) (Sum.elim a id) (hy.symm L g) (id : B → B)
  exact ⟨y, x, hx.symm (L.retarget g) L.value⟩

/-- **Corrected all-instance completeness.** Equality on every finite
instance implies a domain isomorphism matching the prescribed pins up to twins.
Repeated constraints/scopes are essential to the premise. This theorem does not
assert the paper's false simple-instance implication. -/
theorem all_instance_completeness (a : V → A) (b : V → B)
    (h : AllPinnedEqual L g a b) :
    ∃ e : A ≃ B, L.IsTargetIso g e ∧
      ∀ v, (L.retarget g).Twins (e (a v)) (b v) := by
  classical
  obtain ⟨y, x, hxy⟩ := exists_both_surjective_extension L g a b h
  let a' : (V ⊕ A) ⊕ B → A := Sum.elim (Sum.elim a id) x
  let b' : (V ⊕ A) ⊕ B → B := Sum.elim (Sum.elim b y) id
  have ha' : Function.Surjective a' := fun z => ⟨Sum.inl (Sum.inr z), rfl⟩
  have hb' : Function.Surjective b' := fun z => ⟨Sum.inr z, rfl⟩
  have hdiag : SameAtomicDiagram L g a' b' :=
    sameAtomicDiagram_of_allPinnedEqual L g a' b' hxy
  have hcard := twin_class_card_eq_of_allPinnedEqual L g a' b' hxy ha' hb'
  obtain ⟨e, he, hp⟩ := targetIso_of_surjective_diagram_and_twin_card
    L g a' b' hdiag ha' hb' hcard
  exact ⟨e, he, fun v => hp (Sum.inl (Sum.inl v))⟩

/-- The separately labelled all-instance statement is an exact equivalence:
soundness is the original literal change-of-variables/twin-invariance proof. -/
theorem all_instance_pinned_iso_iff (a : V → A) (b : V → B) :
    AllPinnedEqual L g a b ↔
      ∃ e : A ≃ B, L.IsTargetIso g e ∧
        ∀ v, (L.retarget g).Twins (e (a v)) (b v) := by
  constructor
  · exact all_instance_completeness L g a b
  · rintro ⟨e, he, hp⟩ H hH dH I
    exact I.partition_eq_of_iso_pin_twins g e he a b hp

/-- The existing finite candidate checker is complete for the proved repair's
all-instance premise. It is not thereby complete for the paper's simple premise. -/
theorem pinnedIsoCheck_correct_all_instances
    [DecidableEq A] [DecidableEq B] [DecidableEq K] [Fintype ι] [Fintype V]
    (a : V → A) (b : V → B) :
    L.pinnedIsoCheck g a b = true ↔ AllPinnedEqual L g a b := by
  rw [Language.pinnedIsoCheck_eq_true]
  exact (all_instance_pinned_iso_iff L g a b).symm

/-- An actual finite decision procedure for the all-instance property.
It uses the supplied finite domains/signature and coefficient equality; no
classical equality procedure is installed. This is deliberately a named value,
not a global instance silently changing the original development's scope. -/
def allInstanceEqualityDecision
    [DecidableEq A] [DecidableEq B] [DecidableEq K] [Fintype ι] [Fintype V]
    (a : V → A) (b : V → B) : Decidable (AllPinnedEqual L g a b) :=
  decidable_of_iff (L.pinnedIsoCheck g a b = true)
    (pinnedIsoCheck_correct_all_instances L g a b)

/-- Rejection of the finite checker has an actual finite-instance witness.
This is a witness-existence result, not a bound on the smallest counterexample. -/
theorem pinnedIsoCheck_rejects_all_instances
    [DecidableEq A] [DecidableEq B] [DecidableEq K] [Fintype ι] [Fintype V]
    (a : V → A) (b : V → B) :
    L.pinnedIsoCheck g a b = false ↔
      ∃ (H : Type) (_ : Fintype H) (_ : DecidableEq H),
        ∃ I : Instance L V H, I.partition a ≠ (I.retarget g).partition b := by
  classical
  rw [← Bool.not_eq_true, pinnedIsoCheck_correct_all_instances]
  simp only [AllPinnedEqual, not_forall]

end PinnedIsomorphism

end ComplexCSP
