import Paper2.HeightOne.PhaseCards.DiagonalFieldSaturation
import Paper2.SourceFaithful.FactorClosure
import Paper2.SourceFaithful.GadgetAugmentation

/-! Full finite actual card/factor saturation using canonical fixed-field
oracle answers. The pure finite recursion, exact factor decompositions and
frozen-field transport are reused; each encoded reduction is reconstructed
from its source-convention input and composed in that same convention. -/
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable ExactInput GroupSplit

theorem source_adjoin_actual_prime_factors
    (PG : SourceFaithful.Paper1DirectGadgetAccepted) (PR : SourceFaithful.Paper1RestrictionAccepted)
    (PF : SourceFaithful.Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    {n : ℕ} (f : Signature AlgebraicComplex n) (hn : 0 < n) (hf : f ≠ 0)
    (hreal : NetworkRealizable L.family f)
    (Q : TensorDecomposition AlgebraicComplex n) (hQ : Q.value = f)
    (hpos : ∀ i, 0 < Q.arity i) (hprime : ∀ i, TensorPrime (Q.factor i)) :
    ∃ M : Language, L.family ⊆ M.family ∧
      (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      (∀ i, (⟨Q.arity i, Q.factor i⟩ : AnySignature AlgebraicComplex) ∈ M.family) ∧
      Preprocessed M.family ∧ ¬ CommonOneSided M.family ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  obtain ⟨A, hA, hAL, hLA⟩ := PG.adjoin_equivalence PR L f
    (NativeNetworkRealizesUpTo.of_realizable hreal)
  have hsub : L.family ⊆ A.family := by rw [hA]; exact Set.subset_insert _ _
  have hmem : (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ A.family := by rw [hA]; simp
  have hpre : Preprocessed A.family := by
    rw [hA]
    intro g hg
    rcases hg with rfl | hg
    · exact ⟨hn, hf⟩
    · exact hL g hg
  have htwoA : ¬ CommonOneSided A.family := by
    intro h
    apply htwo
    rcases h with h | h
    · exact Or.inl (fun g hg => h g (hsub hg))
    · exact Or.inr (fun g hg => h g (hsub hg))
  obtain ⟨M, hAM, hfac, hpreM, htwoM, hMA, hAMred⟩ :=
    SourceFaithful.factorClosure_with_member_decomposition PF A hpre htwoA f hmem Q hQ hpos hprime
  exact ⟨M, hsub.trans hAM, hAM hmem, hfac, hpreM, htwoM,
    hMA.trans hAL, hLA.trans hAMred⟩


structure SourceRetainedExtension (L M : Language) : Prop where
  subset : L.family ⊆ M.family
  preprocessed : Preprocessed M.family
  notOneSided : ¬ CommonOneSided M.family
  backward : FixedFieldOutput.Reduces .nativeX M L
  forward : FixedFieldOutput.Reduces .nativeX L M

namespace SourceRetainedExtension

lemma refl (PR : SourceFaithful.Paper1RestrictionAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family) : SourceRetainedExtension L L :=
  ⟨Set.Subset.refl _, hL, htwo, PR.restriction_2_5 L L (Set.Subset.refl _),
    PR.restriction_2_5 L L (Set.Subset.refl _)⟩

lemma trans {L M N : Language} (hLM : SourceRetainedExtension L M) (hMN : SourceRetainedExtension M N) :
    SourceRetainedExtension L N :=
  ⟨hLM.subset.trans hMN.subset, hMN.preprocessed, hMN.notOneSided,
    hMN.backward.trans hLM.backward, hLM.forward.trans hMN.forward⟩

/-- Finite iteration of retained exact-input extensions. Each step must supply
its real reductions, and previously established properties must be monotone
under literal resource inclusion. -/
theorem finite_fold {I : Type} [Fintype I] (PR : SourceFaithful.Paper1RestrictionAccepted)
    (L : Language) (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (P : I → Language → Prop)
    (hmono : ∀ i A B, A.family ⊆ B.family → P i A → P i B)
    (hstep : ∀ i A, SourceRetainedExtension L A → ∃ B, SourceRetainedExtension A B ∧ P i B) :
    ∃ M, SourceRetainedExtension L M ∧ ∀ i, P i M := by
  classical
  have aux : ∀ S : Finset I, ∃ M, SourceRetainedExtension L M ∧ ∀ i ∈ S, P i M := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨L, refl PR L hL htwo, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨A, hA, hPA⟩ := ih
      obtain ⟨B, hB, hiB⟩ := hstep i A hA
      refine ⟨B, hA.trans hB, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hiB
      · exact hmono j A B hB.subset (hPA j hj)
  obtain ⟨M, hM, hP⟩ := aux Finset.univ
  exact ⟨M, hM, fun i => hP i (Finset.mem_univ i)⟩

end SourceRetainedExtension

namespace BinaryMenu
variable {F : SignatureFamily AlgebraicComplex} (M : BinaryMenu F)

/-- Process one indicated oriented card using an actual graph and the chosen
prime factorization. Zero/nullary cards contribute no positive factor. -/
theorem source_extend_one_card
    (PG : SourceFaithful.Paper1DirectGadgetAccepted) (PR : SourceFaithful.Paper1RestrictionAccepted)
    (PF : SourceFaithful.Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hFL : F ⊆ L.family) (f : AnySignature AlgebraicComplex) (hf : f ∈ L.family)
    (k : M.Choices f) :
    ∃ A : Language, SourceRetainedExtension L A ∧ selectedFactors (M.produced f k) ⊆ A.family ∧
      (0 < (M.produced f k).1 → (M.produced f k).2 ≠ 0 → M.produced f k ∈ A.family) := by
  let g := M.produced f k
  by_cases hg : 0 < g.1 ∧ g.2 ≠ 0
  · let Q := selectedDecomposition g hg
    have hQ := selectedDecomposition_spec g hg
    obtain ⟨A, hsub, hmem, hfac, hpre, htwoA, hAL, hLA⟩ :=
      source_adjoin_actual_prime_factors PG PR PF L hL htwo g.2 hg.1 hg.2
        (M.produced_realizable hFL f hf k) Q hQ.1 hQ.2.1 hQ.2.2
    refine ⟨A, ⟨hsub, hpre, htwoA, hAL, hLA⟩, ?_, fun _ _ => hmem⟩
    intro p hp
    change p ∈ selectedFactors g at hp
    rw [selectedFactors, dif_pos hg] at hp
    obtain ⟨i, rfl⟩ := hp
    exact hfac i
  · refine ⟨L, SourceRetainedExtension.refl PR L hL htwo, ?_, ?_⟩
    · change selectedFactors g ⊆ L.family
      rw [selectedFactors, dif_neg hg]
      exact Set.empty_subset _
    · intro hp hn
      exact False.elim (hg ⟨hp, hn⟩)

/-- Process every representative/orientation/ordered-pair choice of one retained
parent, with finitely many actual equivalent enlargements. -/
theorem source_extend_parent
    (PG : SourceFaithful.Paper1DirectGadgetAccepted) (PR : SourceFaithful.Paper1RestrictionAccepted)
    (PF : SourceFaithful.Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hFL : F ⊆ L.family) (f : AnySignature AlgebraicComplex) (hf : f ∈ L.family) :
    ∃ A : Language, SourceRetainedExtension L A ∧ M.children f ⊆ A.family ∧
      (∀ k : M.Choices f, 0 < (M.produced f k).1 → (M.produced f k).2 ≠ 0 →
        M.produced f k ∈ A.family) := by
  let P : M.Choices f → Language → Prop := fun k A =>
    selectedFactors (M.produced f k) ⊆ A.family ∧
      (0 < (M.produced f k).1 → (M.produced f k).2 ≠ 0 → M.produced f k ∈ A.family)
  obtain ⟨A, hA, hP⟩ := SourceRetainedExtension.finite_fold PR L hL htwo P
    (fun k A B hAB hP => ⟨hP.1.trans hAB, fun hp hn => hAB (hP.2 hp hn)⟩)
    (fun k A hA => M.source_extend_one_card PG PR PF A hA.preprocessed hA.notOneSided
      (hFL.trans hA.subset) f (hA.subset hf) k)
  refine ⟨A, hA, ?_, fun k => (hP k).2⟩
  intro g hg
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hg
  exact (hP k).1 hk

end BinaryMenu

namespace BinaryMenu
variable {F : SignatureFamily AlgebraicComplex} (M : BinaryMenu F)

theorem source_extend_full_descendants
    (PG : SourceFaithful.Paper1DirectGadgetAccepted) (PR : SourceFaithful.Paper1RestrictionAccepted)
    (PF : SourceFaithful.Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hFL : F ⊆ L.family) (f : AnySignature AlgebraicComplex) (hf : f ∈ L.family) :
    ∃ A : Language, SourceRetainedExtension L A ∧
      ∀ g, Relation.ReflTransGen (fun a b => b ∈ M.next a) f g → M.Processed g A := by
  have aux : ∀ n, ∀ L : Language, Preprocessed L.family → ¬ CommonOneSided L.family →
      F ⊆ L.family → ∀ f : AnySignature AlgebraicComplex, f ∈ L.family → f.1 = n →
      ∃ A : Language, SourceRetainedExtension L A ∧
        ∀ g, Relation.ReflTransGen (fun a b => b ∈ M.next a) f g → M.Processed g A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro L hL htwo hFL f hf hn
      obtain ⟨A, hLA, hchildren, hcards⟩ := M.source_extend_parent PG PR PF L hL htwo hFL f hf
      have hpA : M.Processed f A := ⟨hLA.subset hf, hchildren, hcards⟩
      letI : Fintype (M.next f) := (M.next_finite f).fintype
      let P : M.next f → Language → Prop := fun child B =>
        ∀ g, Relation.ReflTransGen (fun a b => b ∈ M.next a) child.val g → M.Processed g B
      have hstep : ∀ child B, SourceRetainedExtension A B → ∃ C, SourceRetainedExtension B C ∧ P child C := by
        intro child B hAB
        have hlt : child.val.1 < n := by have hc := M.next_arity child.property; omega
        exact ih child.val.1 hlt B hAB.preprocessed hAB.notOneSided
          (hFL.trans (hLA.subset.trans hAB.subset)) child.val
          (hAB.subset (M.processed_next hpA child.property)) rfl
      obtain ⟨B, hAB, hP⟩ := SourceRetainedExtension.finite_fold PR A hLA.preprocessed hLA.notOneSided P
        (fun child A B hAB hPA g hg => (hPA g hg).mono M hAB) hstep
      refine ⟨B, hLA.trans hAB, ?_⟩
      intro g hg
      rcases hg.cases_head with he | ⟨child, hc, hcg⟩
      · subst g
        exact hpA.mono M hAB.subset
      · exact hP ⟨child, hc⟩ g hcg
  exact aux f.1 L hL htwo hFL f hf rfl

end BinaryMenu


theorem source_exists_retained_factorClosed
    (PF : SourceFaithful.Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family) :
    ∃ A : Language, SourceRetainedExtension L A ∧ FactorClosed A.family := by
  obtain ⟨D, A, hA, hAL, hLA⟩ := SourceFaithful.factorClosure_exists PF L hL htwo
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

theorem source_finite_factor_closed_saturation
    (PG : SourceFaithful.Paper1DirectGadgetAccepted) (PR : SourceFaithful.Paper1RestrictionAccepted)
    (PF : SourceFaithful.Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hFL : F ⊆ L.family) (hfac : FactorClosed L.family) :
    ∃ B : Language, SourceRetainedExtension L B ∧ FactorClosed B.family ∧
      (∀ f ∈ B.family, M.Processed f B) ∧
      (∀ g ∈ B.family, ∃ f ∈ L.family,
        Relation.ReflTransGen (fun a b => b ∈ M.next a) f g) := by
  obtain ⟨T, hTf, hLT, hclosed, hreach⟩ := M.finite_full_subtree L.family L.family_finite
  have hpreFac := M.full_subtree_factorClosed L hL hfac T hLT hclosed hreach
  letI : Fintype L.family := L.family_finite.fintype
  let P : L.family → Language → Prop := fun root A =>
    ∀ g, Relation.ReflTransGen (fun a b => b ∈ M.next a) root.val g → M.Processed g A
  obtain ⟨A, hLA, hPA⟩ := SourceRetainedExtension.finite_fold PR L hL htwo P
    (fun root A B hAB hPA g hg => (hPA g hg).mono M hAB)
    (fun root A hA => M.source_extend_full_descendants PG PR PF A hA.preprocessed hA.notOneSided
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

theorem source_finite_factor_closed_saturation_pullback
    (PG : SourceFaithful.Paper1DirectGadgetAccepted) (PR : SourceFaithful.Paper1RestrictionAccepted)
    (PF : SourceFaithful.Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hFL : F ⊆ L.family) (hfac : FactorClosed L.family)
    (E : Subfield AlgebraicComplex) (A : InvertibleKernel)
    (a b : AlgebraicComplex) (hA : A.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfield : ∀ f ∈ L.family, PullbackOver E A f) :
    ∃ B : Language, SourceRetainedExtension L B ∧ FactorClosed B.family ∧
      (∀ f ∈ B.family, M.Processed f B) ∧ (∀ f ∈ B.family, PullbackOver E A f) := by
  obtain ⟨B, hB, hfacB, hprocessed, hreach⟩ :=
    M.source_finite_factor_closed_saturation PG PR PF L hL htwo hFL hfac
  refine ⟨B, hB, hfacB, hprocessed, ?_⟩
  intro g hg
  obtain ⟨f, hf, hfg⟩ := hreach g hg
  have hF : ∀ f ∈ F, PullbackOver E A f := fun f hf => hfield f (hFL hf)
  clear hg
  induction hfg with
  | refl => exact hfield f hf
  | tail _ hb' ih => exact M.next_pullbackOver E A a b hA ha hb hF ih hb'

end BinaryMenu

end
end Paper2.HeightOne.PhaseCards

