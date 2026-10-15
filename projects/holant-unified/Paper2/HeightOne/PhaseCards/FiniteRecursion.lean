import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-! The finite recursive-subtree argument used for contraction-factor cards.
Strict arity decrease, rather than a false strict group update at each card,
is what makes the finitely branching inner closure finite. -/
namespace Paper2.HeightOne.PhaseCards

/-- A finitely branching relation whose natural rank strictly decreases has
only finitely many descendants of any fixed object. -/
theorem finite_descendants {α : Type*} (rank : α → ℕ) (R : α → α → Prop)
    (hfinite : ∀ a, {b | R a b}.Finite)
    (hdecrease : ∀ a b, R a b → rank b < rank a) (a : α) :
    {b | Relation.ReflTransGen R a b}.Finite := by
  have aux : ∀ n a, rank a = n → {b | Relation.ReflTransGen R a b}.Finite := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha
      have hc : (⋃ b ∈ {b | R a b}, {c | Relation.ReflTransGen R b c}).Finite :=
        (hfinite a).biUnion (fun b hb => ih (rank b) (ha ▸ hdecrease a b hb) b rfl)
      apply ((Set.finite_singleton a).union hc).subset
      intro b hb
      rcases hb.cases_head with he | ⟨c, hac, hcb⟩
      · exact Or.inl he.symm
      · exact Or.inr (Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hac, hcb⟩⟩)
  exact aux (rank a) a rfl

/-- A finite set of roots has a finite exhaustive recursive closure. Equal-group
saturation is allowed: no outer strict-progress claim occurs in this theorem. -/
theorem finite_recursive_closure {α : Type*} (rank : α → ℕ) (R : α → α → Prop)
    (hfinite : ∀ a, {b | R a b}.Finite)
    (hdecrease : ∀ a b, R a b → rank b < rank a)
    (S : Set α) (hS : S.Finite) :
    ∃ T : Set α, T.Finite ∧ S ⊆ T ∧ (∀ a ∈ T, ∀ b, R a b → b ∈ T) ∧
      (∀ b ∈ T, ∃ a ∈ S, Relation.ReflTransGen R a b) := by
  let T : Set α := ⋃ a ∈ S, {b | Relation.ReflTransGen R a b}
  refine ⟨T, hS.biUnion (fun a _ => finite_descendants rank R hfinite hdecrease a), ?_, ?_, ?_⟩
  · intro a ha
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, Relation.ReflTransGen.refl⟩⟩
  · intro a ha b hab
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp ha
    obtain ⟨hcS, hca⟩ := Set.mem_iUnion.mp hc
    exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hcS, hca.tail hab⟩⟩
  · intro b hb
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hb
    obtain ⟨haS, hab⟩ := Set.mem_iUnion.mp ha
    exact ⟨a, haS, hab⟩

end Paper2.HeightOne.PhaseCards
