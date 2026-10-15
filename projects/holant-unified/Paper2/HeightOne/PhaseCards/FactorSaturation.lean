import Paper2.HeightOne.PhaseCards.FullRecursion

/-! A precise finite retained language, rather than the arbitrary superset
returned by repeated extraction. Every actual label has an explicit prime
factorization inside that same language, and every indicated card is processed.
The fixed-field ledger and terminal/group-update trichotomy are separate. -/
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable ExactInput

/-- Literal factor closure means that each retained label has a genuine ordered
prime decomposition whose positive factors are retained. It does not quantify
over all scalar multiples of all factors, which would be an infinite family. -/
def FactorClosed (F : SignatureFamily AlgebraicComplex) : Prop :=
  ∀ f ∈ F, ∃ D : TensorDecomposition AlgebraicComplex f.1,
    D.value = f.2 ∧ (∀ i, 0 < D.arity i) ∧ (∀ i, TensorPrime (D.factor i)) ∧
      (∀ i, (⟨D.arity i, D.factor i⟩ : AnySignature AlgebraicComplex) ∈ F)

lemma factorClosed_retained {L : Language} (D : PrimeFactorization L) :
    FactorClosed (L.family ∪ D.factors) := by
  intro f hf
  rcases hf with ⟨i, rfl⟩ | ⟨⟨i, j⟩, rfl⟩
  · exact ⟨D.decomposition i, D.exact_value i, D.positive i, D.prime i,
      fun j => Or.inr ⟨⟨i, j⟩, rfl⟩⟩
  · refine ⟨TensorDecomposition.singleton ((D.decomposition i).factor j),
      TensorDecomposition.value_singleton _, fun _ => D.positive i j,
      fun _ => D.prime i j, ?_⟩
    intro k
    exact Or.inr ⟨⟨i, j⟩, rfl⟩

/-- One accepted source factor-extraction step suffices to obtain actual finite
factor closure; no factor-closure theorem is added to the assumptions. -/
theorem exists_retained_factorClosed
    (PF : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family) :
    ∃ A : Language, RetainedExtension L A ∧ FactorClosed A.family := by
  obtain ⟨D, A, hA, hAL, hLA⟩ := factorClosure_exists PF L hL htwo
  have hsub : L.family ⊆ A.family := by rw [hA]; exact Set.subset_union_left
  refine ⟨A, ⟨hsub, ?_, ?_, hAL, hLA⟩, ?_⟩
  · rw [hA]
    exact D.retained_preprocessed hL
  · intro hs
    apply htwo
    rcases hs with hs | hs
    · exact Or.inl (fun f hf => hs f (hsub hf))
    · exact Or.inr (fun f hf => hs f (hsub hf))
  · rw [hA]
    exact factorClosed_retained D

namespace BinaryMenu
variable {F : SignatureFamily AlgebraicComplex} (M : BinaryMenu F)

lemma reach_mem {T : Set (AnySignature AlgebraicComplex)}
    (hT : ∀ f ∈ T, M.next f ⊆ T) {f g : AnySignature AlgebraicComplex}
    (hf : f ∈ T) (hg : Relation.ReflTransGen (fun a b => b ∈ M.next a) f g) : g ∈ T := by
  induction hg with
  | refl => exact hf
  | tail _ hb ih => exact hT _ ih hb

/-- A finite exhaustive actual-card closure remains preprocessed and genuinely
factor-closed. Both ordinary cards and prime factors occur in the recursion. -/
lemma full_subtree_factorClosed (L : Language) (hL : Preprocessed L.family)
    (hfac : FactorClosed L.family) (T : Set (AnySignature AlgebraicComplex))
    (hLT : L.family ⊆ T) (hclosed : ∀ f ∈ T, M.next f ⊆ T)
    (hreach : ∀ g ∈ T, ∃ f ∈ L.family,
      Relation.ReflTransGen (fun a b => b ∈ M.next a) f g) :
    Preprocessed T ∧ FactorClosed T := by
  constructor
  · intro g hg
    obtain ⟨f, hf, hfg⟩ := hreach g hg
    rcases hfg.cases_tail with rfl | ⟨p, hp, hpg⟩
    · exact hL _ hf
    · exact M.next_preprocessed hpg
  · intro g hg
    obtain ⟨f, hf, hfg⟩ := hreach g hg
    rcases hfg.cases_tail with rfl | ⟨p, hp, hpg⟩
    · obtain ⟨D, hD, hpos, hprime, hmem⟩ := hfac _ hf
      exact ⟨D, hD, hpos, hprime, fun i => hLT (hmem i)⟩
    · have hpT : p ∈ T := M.reach_mem hclosed (hLT hf) hp
      rcases hpg with hc | ⟨k, rfl, hpos, hn⟩
      · have hc' := M.child_arity hc
        exact ⟨TensorDecomposition.singleton g.2,
          TensorDecomposition.value_singleton _, fun _ => hc'.1,
          fun _ => hc'.2.1, fun _ => hg⟩
      · let Q := selectedDecomposition (M.produced p k) ⟨hpos, hn⟩
        have hQ := selectedDecomposition_spec (M.produced p k) ⟨hpos, hn⟩
        refine ⟨Q, hQ.1, hQ.2.1, hQ.2.2, ?_⟩
        intro i
        apply hclosed p hpT
        left
        apply Set.mem_iUnion.mpr
        refine ⟨k, ?_⟩
        rw [selectedFactors, dif_pos ⟨hpos, hn⟩]
        exact ⟨i, rfl⟩

/-- Finite actual saturation with no uncontrolled extra labels. This closes the
full-language factor-closure gap in the earlier selected-factor subtree lemma.
The conclusion concerns a fixed menu, and does not assume binary safety or an
unchanged complete projective group. -/
theorem finite_factor_closed_saturation
    (PG : Paper1DirectGadgetAccepted) (PR : Paper1RestrictionAccepted)
    (PF : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hFL : F ⊆ L.family) (hfac : FactorClosed L.family) :
    ∃ B : Language, RetainedExtension L B ∧ FactorClosed B.family ∧
      (∀ f ∈ B.family, M.Processed f B) ∧
      (∀ g ∈ B.family, ∃ f ∈ L.family,
        Relation.ReflTransGen (fun a b => b ∈ M.next a) f g) := by
  obtain ⟨T, hTf, hLT, hclosed, hreach⟩ := M.finite_full_subtree L.family L.family_finite
  have hpreFac := M.full_subtree_factorClosed L hL hfac T hLT hclosed hreach
  letI : Fintype L.family := L.family_finite.fintype
  let P : L.family → Language → Prop := fun root A =>
    ∀ g, Relation.ReflTransGen (fun a b => b ∈ M.next a) root.val g → M.Processed g A
  obtain ⟨A, hLA, hPA⟩ := RetainedExtension.finite_fold PR L hL htwo P
    (fun root A B hAB hPA g hg => (hPA g hg).mono M hAB)
    (fun root A hA => M.extend_full_descendants PG PR PF A hA.preprocessed hA.notOneSided
      (hFL.trans hA.subset) root.val (hA.subset root.property))
  have hTA : T ⊆ A.family := by
    intro g hg
    obtain ⟨f, hf, hfg⟩ := hreach g hg
    exact (hPA ⟨f, hf⟩ g hfg).1
  obtain ⟨B, hB⟩ := Language.coverage_family T hTf
  have hLB : L.family ⊆ B.family := by rwa [hB]
  have hBA : B.family ⊆ A.family := by rwa [hB]
  refine ⟨B, ⟨hLB, ?_, ?_, (PR.restriction_2_5 B A hBA).trans hLA.backward,
    PR.restriction_2_5 L B hLB⟩, ?_, ?_, ?_⟩
  · simpa only [hB] using hpreFac.1
  · intro hs
    apply htwo
    rcases hs with hs | hs
    · exact Or.inl (fun f hf => hs f (hLB hf))
    · exact Or.inr (fun f hf => hs f (hLB hf))
  · simpa only [hB] using hpreFac.2
  · intro f hf
    refine ⟨hf, ?_, ?_⟩
    · intro g hg
      rw [hB] at hf ⊢
      exact hclosed f hf (Or.inl hg)
    · intro k hp hn
      rw [hB] at hf ⊢
      exact hclosed f hf (Or.inr ⟨k, rfl, hp, hn⟩)
  · rwa [hB]

end BinaryMenu
end
end Paper2.HeightOne.PhaseCards
