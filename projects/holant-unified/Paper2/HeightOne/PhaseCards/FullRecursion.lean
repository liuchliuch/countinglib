import Paper2.HeightOne.PhaseCards.SaturationCore

/-! Full finite recursive processing includes both the actual card itself and
all its chosen prime factors. Processing only factors omits prime card labels
which differ from the chosen factor by a nonzero normalization scalar. -/
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable ExactInput
namespace BinaryMenu
variable {F : SignatureFamily AlgebraicComplex} (M : BinaryMenu F)

/-- Every nonzero positive-arity card, with both orientations and every ordered
pair retained literally. -/
def positiveCards (f : AnySignature AlgebraicComplex) : Set (AnySignature AlgebraicComplex) :=
  {g | ∃ k : M.Choices f, M.produced f k = g ∧ 0 < g.1 ∧ g.2 ≠ 0}

lemma positiveCards_finite (f : AnySignature AlgebraicComplex) :
    (M.positiveCards f).Finite := by
  apply (Set.finite_range (M.produced f)).subset
  rintro g ⟨k, rfl, hg⟩
  exact ⟨k, rfl⟩

/-- Both child types have arity at least two below the parent. -/
def next (f : AnySignature AlgebraicComplex) : Set (AnySignature AlgebraicComplex) :=
  M.children f ∪ M.positiveCards f

lemma next_finite (f : AnySignature AlgebraicComplex) : (M.next f).Finite :=
  (M.children_finite f).union (M.positiveCards_finite f)

lemma next_preprocessed {f g : AnySignature AlgebraicComplex} (hg : g ∈ M.next f) :
    0 < g.1 ∧ g.2 ≠ 0 := by
  rcases hg with hg | ⟨k, rfl, hp, hn⟩
  · exact ⟨(M.child_arity hg).1, (M.child_arity hg).2.1.1⟩
  · exact ⟨hp, hn⟩

lemma next_arity {f g : AnySignature AlgebraicComplex} (hg : g ∈ M.next f) :
    g.1 + 2 ≤ f.1 := by
  rcases hg with hg | ⟨k, rfl, _⟩
  · exact (M.child_arity hg).2.2
  · exact (M.produced_arity f k).le

lemma processed_next {f : AnySignature AlgebraicComplex} {L : Language}
    (h : M.Processed f L) : M.next f ⊆ L.family := by
  intro g hg
  rcases hg with hg | ⟨k, rfl, hp, hn⟩
  · exact h.2.1 hg
  · exact h.2.2 k hp hn

/-- Strong arity induction processes cards as well as their prime factors.
The supplied reductions are actual finite-language reductions at every step. -/
theorem extend_full_descendants
    (PG : Paper1DirectGadgetAccepted) (PR : Paper1RestrictionAccepted)
    (PF : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hFL : F ⊆ L.family) (f : AnySignature AlgebraicComplex) (hf : f ∈ L.family) :
    ∃ A : Language, RetainedExtension L A ∧
      ∀ g, Relation.ReflTransGen (fun a b => b ∈ M.next a) f g → M.Processed g A := by
  have aux : ∀ n, ∀ L : Language, Preprocessed L.family → ¬ CommonOneSided L.family →
      F ⊆ L.family → ∀ f : AnySignature AlgebraicComplex, f ∈ L.family → f.1 = n →
      ∃ A : Language, RetainedExtension L A ∧
        ∀ g, Relation.ReflTransGen (fun a b => b ∈ M.next a) f g → M.Processed g A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro L hL htwo hFL f hf hn
      obtain ⟨A, hLA, hchildren, hcards⟩ := M.extend_parent PG PR PF L hL htwo hFL f hf
      have hpA : M.Processed f A := ⟨hLA.subset hf, hchildren, hcards⟩
      letI : Fintype (M.next f) := (M.next_finite f).fintype
      let P : M.next f → Language → Prop := fun child B =>
        ∀ g, Relation.ReflTransGen (fun a b => b ∈ M.next a) child.val g → M.Processed g B
      have hstep : ∀ child B, RetainedExtension A B → ∃ C, RetainedExtension B C ∧ P child C := by
        intro child B hAB
        have hlt : child.val.1 < n := by have hc := M.next_arity child.property; omega
        exact ih child.val.1 hlt B hAB.preprocessed hAB.notOneSided
          (hFL.trans (hLA.subset.trans hAB.subset)) child.val
          (hAB.subset (M.processed_next hpA child.property)) rfl
      obtain ⟨B, hAB, hP⟩ := RetainedExtension.finite_fold PR A hLA.preprocessed hLA.notOneSided P
        (fun child A B hAB hPA g hg => (hPA g hg).mono M hAB) hstep
      refine ⟨B, hLA.trans hAB, ?_⟩
      intro g hg
      rcases hg.cases_head with he | ⟨child, hc, hcg⟩
      · subst g
        exact hpA.mono M hAB.subset
      · exact hP ⟨child, hc⟩ g hcg
  exact aux f.1 L hL htwo hFL f hf rfl

/-- Exhaustive finite closure of the literal card-and-factor relation. -/
theorem finite_full_subtree (S : Set (AnySignature AlgebraicComplex)) (hS : S.Finite) :
    ∃ T : Set (AnySignature AlgebraicComplex), T.Finite ∧ S ⊆ T ∧
      (∀ f ∈ T, M.next f ⊆ T) ∧
      (∀ g ∈ T, ∃ f ∈ S, Relation.ReflTransGen (fun a b => b ∈ M.next a) f g) :=
  finite_recursive_closure (fun f => f.1) (fun a b => b ∈ M.next a)
    M.next_finite (fun a b h => by have := M.next_arity h; omega) S hS

end BinaryMenu
end
end Paper2.HeightOne.PhaseCards
