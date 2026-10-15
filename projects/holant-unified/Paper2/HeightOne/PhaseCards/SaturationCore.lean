import Paper2.HeightOne.PhaseCards.RetainedExtension

/-! Finite equivalent enlargement processing the entire actual selected-factor
subtree. This is the finite-recursion/reduction core of source Lemma 5.8; it does
not assert safety or unchanged group for the final language. -/
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable ExactInput
namespace BinaryMenu
variable {F : SignatureFamily AlgebraicComplex} (M : BinaryMenu F)

/-- A parent, every positive selected prime factor, and every nonzero
positive-arity indicated card have actually been retained. -/
def Processed (f : AnySignature AlgebraicComplex) (L : Language) : Prop :=
  f ∈ L.family ∧ M.children f ⊆ L.family ∧
    ∀ k : M.Choices f, 0 < (M.produced f k).1 → (M.produced f k).2 ≠ 0 →
      M.produced f k ∈ L.family

lemma Processed.mono {f : AnySignature AlgebraicComplex} {L A : Language}
    (h : M.Processed f L) (hLA : L.family ⊆ A.family) : M.Processed f A :=
  ⟨hLA h.1, h.2.1.trans hLA, fun k hp hn => hLA (h.2.2 k hp hn)⟩

/-- Strong induction on literal arity composes all actual child-card and
factor-extraction reductions, not merely the abstract cardinality argument. -/
theorem extend_descendants
    (PG : Paper1DirectGadgetAccepted) (PR : Paper1RestrictionAccepted)
    (PF : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hFL : F ⊆ L.family) (f : AnySignature AlgebraicComplex) (hf : f ∈ L.family) :
    ∃ A : Language, RetainedExtension L A ∧
      ∀ g, Relation.ReflTransGen (fun a b => b ∈ M.children a) f g → M.Processed g A := by
  have aux : ∀ n, ∀ L : Language, Preprocessed L.family → ¬ CommonOneSided L.family →
      F ⊆ L.family → ∀ f : AnySignature AlgebraicComplex, f ∈ L.family → f.1 = n →
      ∃ A : Language, RetainedExtension L A ∧
        ∀ g, Relation.ReflTransGen (fun a b => b ∈ M.children a) f g → M.Processed g A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro L hL htwo hFL f hf hn
      obtain ⟨A, hLA, hchildren, hcards⟩ := M.extend_parent PG PR PF L hL htwo hFL f hf
      have hpA : M.Processed f A := ⟨hLA.subset hf, hchildren, hcards⟩
      letI : Fintype (M.children f) := (M.children_finite f).fintype
      let P : M.children f → Language → Prop := fun child B =>
        ∀ g, Relation.ReflTransGen (fun a b => b ∈ M.children a) child.val g → M.Processed g B
      have hstep : ∀ child B, RetainedExtension A B → ∃ C, RetainedExtension B C ∧ P child C := by
        intro child B hAB
        have hlt : child.val.1 < n := by
          have hc := M.child_arity child.property
          omega
        exact ih child.val.1 hlt B hAB.preprocessed hAB.notOneSided
          (hFL.trans (hLA.subset.trans hAB.subset)) child.val
          (hAB.subset (hchildren child.property)) rfl
      obtain ⟨B, hAB, hP⟩ := RetainedExtension.finite_fold PR A hLA.preprocessed hLA.notOneSided P
        (fun child A B hAB hPA g hg => (hPA g hg).mono M hAB) hstep
      refine ⟨B, hLA.trans hAB, ?_⟩
      intro g hg
      rcases hg.cases_head with he | ⟨child, hc, hcg⟩
      · subst g
        exact hpA.mono M hAB.subset
      · exact hP ⟨child, hc⟩ g hcg
  exact aux f.1 L hL htwo hFL f hf rfl

/-- Finitely many retained roots are simultaneously saturated along every
selected actual card/factor branch, in one finite exact-input language. -/
theorem extend_finite_roots
    (PG : Paper1DirectGadgetAccepted) (PR : Paper1RestrictionAccepted)
    (PF : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hFL : F ⊆ L.family) (S : Set (AnySignature AlgebraicComplex)) (hS : S.Finite)
    (hSL : S ⊆ L.family) :
    ∃ A : Language, RetainedExtension L A ∧
      ∀ f ∈ S, ∀ g, Relation.ReflTransGen (fun a b => b ∈ M.children a) f g → M.Processed g A := by
  letI : Fintype S := hS.fintype
  let P : S → Language → Prop := fun root A =>
    ∀ g, Relation.ReflTransGen (fun a b => b ∈ M.children a) root.val g → M.Processed g A
  obtain ⟨A, hA, hP⟩ := RetainedExtension.finite_fold PR L hL htwo P
    (fun root A B hAB hPA g hg => (hPA g hg).mono M hAB)
    (fun root A hA => M.extend_descendants PG PR PF A hA.preprocessed hA.notOneSided
      (hFL.trans hA.subset) root.val (hA.subset (hSL root.property)))
  exact ⟨A, hA, fun f hf => hP ⟨f, hf⟩⟩

end BinaryMenu
end
end Paper2.HeightOne.PhaseCards
