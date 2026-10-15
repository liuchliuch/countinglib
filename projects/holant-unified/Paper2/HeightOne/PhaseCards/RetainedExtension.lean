import Paper2.HeightOne.PhaseCards.RecursiveCards

/-! Finite composition of the real card/factor reduction steps. This records
literal retained languages and actual two-way reductions, not an abstract
cost-free adjoin operation. -/
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable ExactInput

structure RetainedExtension (L M : Language) : Prop where
  subset : L.family ⊆ M.family
  preprocessed : Preprocessed M.family
  notOneSided : ¬ CommonOneSided M.family
  backward : Problem.Reduces .nativeX M L
  forward : Problem.Reduces .nativeX L M

namespace RetainedExtension

lemma refl (PR : Paper1RestrictionAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family) : RetainedExtension L L :=
  ⟨Set.Subset.refl _, hL, htwo, PR.restriction_2_5 L L (Set.Subset.refl _),
    PR.restriction_2_5 L L (Set.Subset.refl _)⟩

lemma trans {L M N : Language} (hLM : RetainedExtension L M) (hMN : RetainedExtension M N) :
    RetainedExtension L N :=
  ⟨hLM.subset.trans hMN.subset, hMN.preprocessed, hMN.notOneSided,
    hMN.backward.trans hLM.backward, hLM.forward.trans hMN.forward⟩

/-- Finite iteration of retained exact-input extensions. Each step must supply
its real reductions, and previously established properties must be monotone
under literal resource inclusion. -/
theorem finite_fold {I : Type} [Fintype I] (PR : Paper1RestrictionAccepted)
    (L : Language) (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (P : I → Language → Prop)
    (hmono : ∀ i A B, A.family ⊆ B.family → P i A → P i B)
    (hstep : ∀ i A, RetainedExtension L A → ∃ B, RetainedExtension A B ∧ P i B) :
    ∃ M, RetainedExtension L M ∧ ∀ i, P i M := by
  classical
  have aux : ∀ S : Finset I, ∃ M, RetainedExtension L M ∧ ∀ i ∈ S, P i M := by
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

end RetainedExtension

namespace BinaryMenu
variable {F : SignatureFamily AlgebraicComplex} (M : BinaryMenu F)

/-- Process one indicated oriented card using an actual graph and the chosen
prime factorization. Zero/nullary cards contribute no positive factor. -/
theorem extend_one_card
    (PG : Paper1DirectGadgetAccepted) (PR : Paper1RestrictionAccepted)
    (PF : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hFL : F ⊆ L.family) (f : AnySignature AlgebraicComplex) (hf : f ∈ L.family)
    (k : M.Choices f) :
    ∃ A : Language, RetainedExtension L A ∧ selectedFactors (M.produced f k) ⊆ A.family ∧
      (0 < (M.produced f k).1 → (M.produced f k).2 ≠ 0 → M.produced f k ∈ A.family) := by
  let g := M.produced f k
  by_cases hg : 0 < g.1 ∧ g.2 ≠ 0
  · let Q := selectedDecomposition g hg
    have hQ := selectedDecomposition_spec g hg
    obtain ⟨A, hsub, hmem, hfac, hpre, htwoA, hAL, hLA⟩ :=
      adjoin_actual_prime_factors PG PR PF L hL htwo g.2 hg.1 hg.2
        (M.produced_realizable hFL f hf k) Q hQ.1 hQ.2.1 hQ.2.2
    refine ⟨A, ⟨hsub, hpre, htwoA, hAL, hLA⟩, ?_, fun _ _ => hmem⟩
    intro p hp
    change p ∈ selectedFactors g at hp
    rw [selectedFactors, dif_pos hg] at hp
    obtain ⟨i, rfl⟩ := hp
    exact hfac i
  · refine ⟨L, RetainedExtension.refl PR L hL htwo, ?_, ?_⟩
    · change selectedFactors g ⊆ L.family
      rw [selectedFactors, dif_neg hg]
      exact Set.empty_subset _
    · intro hp hn
      exact False.elim (hg ⟨hp, hn⟩)

/-- Process every representative/orientation/ordered-pair choice of one retained
parent, with finitely many actual equivalent enlargements. -/
theorem extend_parent
    (PG : Paper1DirectGadgetAccepted) (PR : Paper1RestrictionAccepted)
    (PF : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hFL : F ⊆ L.family) (f : AnySignature AlgebraicComplex) (hf : f ∈ L.family) :
    ∃ A : Language, RetainedExtension L A ∧ M.children f ⊆ A.family ∧
      (∀ k : M.Choices f, 0 < (M.produced f k).1 → (M.produced f k).2 ≠ 0 →
        M.produced f k ∈ A.family) := by
  let P : M.Choices f → Language → Prop := fun k A =>
    selectedFactors (M.produced f k) ⊆ A.family ∧
      (0 < (M.produced f k).1 → (M.produced f k).2 ≠ 0 → M.produced f k ∈ A.family)
  obtain ⟨A, hA, hP⟩ := RetainedExtension.finite_fold PR L hL htwo P
    (fun k A B hAB hP => ⟨hP.1.trans hAB, fun hp hn => hAB (hP.2 hp hn)⟩)
    (fun k A hA => M.extend_one_card PG PR PF A hA.preprocessed hA.notOneSided
      (hFL.trans hA.subset) f (hA.subset hf) k)
  refine ⟨A, hA, ?_, fun k => (hP k).2⟩
  intro g hg
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hg
  exact (hP k).1 hk

end BinaryMenu
end
end Paper2.HeightOne.PhaseCards
