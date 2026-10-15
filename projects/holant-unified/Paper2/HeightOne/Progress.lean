import Mathlib.Data.Finset.Card
import Mathlib.Order.WellFounded
import Mathlib.Tactic

/-!
The exact strict-update measure of arXiv:2610.00081v1, Lemma 5.6.
This proves the well-founded integer argument after the finite-subgroup bound
has been established. It does not assume or establish that bound, and it does
not turn arbitrary closure steps into strict updates.
-/
namespace Paper2.HeightOne

/-- Only the cardinality and least remaining nonbinary arity affect the
well-founded measure; the actual group inclusion must be supplied by the
mathematical construction. -/
structure ProgressState where
  groupCard : ℕ
  minArity : ℕ
  minArity_ge_three : 3 ≤ minArity

/-- The displayed measure in Lemma 5.6. -/
def potential (bound : ℕ) (s : ProgressState) : ℕ :=
  (bound - s.groupCard) + (s.minArity - 3)

/-- An update is strict only if one of the two concrete comparisons is strict.
Equal-measure finite recursive saturation is intentionally outside this relation. -/
def StrictUpdate (bound : ℕ) (next current : ProgressState) : Prop :=
  current.groupCard ≤ next.groupCard ∧ next.groupCard ≤ bound ∧
  next.minArity ≤ current.minArity ∧
  (current.groupCard < next.groupCard ∨ next.minArity < current.minArity)

theorem potential_decreases {bound : ℕ} {next current : ProgressState}
    (h : StrictUpdate bound next current) :
    potential bound next < potential bound current := by
  obtain ⟨hcard, hbound, harity, hstrict⟩ := h
  have hn := next.minArity_ge_three
  have hc := current.minArity_ge_three
  unfold potential
  rcases hstrict with hstrict | hstrict <;> omega

theorem strictUpdate_wellFounded (bound : ℕ) : WellFounded (StrictUpdate bound) :=
  (measure (potential bound)).wf.mono (fun _ _ h => potential_decreases h)

/-- A nested finite set strictly grows in cardinality when the inclusion is
proper. This is the group-cardinality input to the measure argument. -/
theorem strictUpdate_of_nested {α : Type*} {H H' : Finset α} {bound ν ν' : ℕ}
    (hν : 3 ≤ ν) (hν' : 3 ≤ ν') (hincl : H ⊆ H')
    (hbound : H'.card ≤ bound) (harity : ν' ≤ ν)
    (hstrict : H ≠ H' ∨ ν' < ν) :
    StrictUpdate bound ⟨H'.card, ν', hν'⟩ ⟨H.card, ν, hν⟩ := by
  refine ⟨Finset.card_le_card hincl, hbound, harity, ?_⟩
  rcases hstrict with hne | hlt
  · left
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hincl, hne⟩)
  · exact Or.inr hlt

/-- In particular, there is no infinite sequence of strict updates satisfying
the fixed bound. -/
theorem no_infinite_strict_updates (bound : ℕ) :
    ¬ ∃ states : ℕ → ProgressState,
      ∀ n, StrictUpdate bound (states (n + 1)) (states n) := by
  rintro ⟨states, hs⟩
  have hdec : ∀ n, potential bound (states (n + 1)) < potential bound (states n) :=
    fun n => potential_decreases (hs n)
  have hbound : ∀ n, potential bound (states n) + n ≤ potential bound (states 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hdec n
      omega
  have := hbound (potential bound (states 0) + 1)
  omega

end Paper2.HeightOne
