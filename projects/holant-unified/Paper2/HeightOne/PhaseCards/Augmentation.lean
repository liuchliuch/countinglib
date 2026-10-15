import Paper2.HeightOne.PhaseCards.Cards
import Paper2.HeightOne.PhaseCards.PrimeParity
import Paper2.Paper1Accepted.Terminals

/-! Actual card augmentation and retained prime-factor extraction. Only the
existing named Paper 1 gadget/restriction/factor interfaces are consumed, and
the original non-common-one-sided hypothesis is retained explicitly. -/
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable ExactInput EndpointSelfLoop

lemma factor_arity_le {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i : Fin D.count) : D.arity i ≤ n := by
  have h := Fintype.card_le_of_injective (fun j : Fin (D.arity i) => D.ports ⟨i, j⟩)
    (fun j k h => by simpa using D.ports.injective h)
  simpa using h

/-- One genuine card and a prescribed complete prime factorization are adjoined
with exact finite languages and two real length-controlled reductions. -/
theorem adjoin_actual_prime_factors
    (PG : Paper1DirectGadgetAccepted) (PR : Paper1RestrictionAccepted)
    (PF : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    {n : ℕ} (f : Signature AlgebraicComplex n) (hn : 0 < n) (hf : f ≠ 0)
    (hreal : NetworkRealizable L.family f)
    (Q : TensorDecomposition AlgebraicComplex n) (hQ : Q.value = f)
    (hpos : ∀ i, 0 < Q.arity i) (hprime : ∀ i, TensorPrime (Q.factor i)) :
    ∃ M : Language, L.family ⊆ M.family ∧
      (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      (∀ i, (⟨Q.arity i, Q.factor i⟩ : AnySignature AlgebraicComplex) ∈ M.family) ∧
      Preprocessed M.family ∧ ¬ CommonOneSided M.family ∧
      Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M := by
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
    factorClosure_with_member_decomposition PF A hpre htwoA f hmem Q hQ hpos hprime
  exact ⟨M, hsub.trans hAM, hAM hmem, hfac, hpreM, htwoM,
    hMA.trans hAL, hLA.trans hAMred⟩

/-- Every nonzero positive-arity native rotation card admits a retained exact
prime-factor augmentation. Each factor loses at least the two contracted ports
from the parent; no strict outer-group update is asserted here. -/
theorem adjoin_rotation_card_factors
    (PG : Paper1DirectGadgetAccepted) (PR : Paper1RestrictionAccepted)
    (PF : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    {N n : ℕ} (C : RotationCards L.family N) (f : Signature AlgebraicComplex n)
    (hf : NetworkRealizable L.family f) (hn : 3 ≤ n)
    (a b : Fin n) (hab : a ≠ b) (s : rootsOfUnity N AlgebraicComplex)
    (hcard : C.contraction a b hab s f ≠ 0) :
    ∃ (Q : TensorDecomposition AlgebraicComplex (Fintype.card (Remaining a b)))
      (M : Language),
      Tensor.reindex (Fintype.equivFin (Remaining a b)).symm Q.value = C.contraction a b hab s f ∧
      (∀ i, 0 < Q.arity i ∧ TensorPrime (Q.factor i) ∧ Q.arity i + 2 ≤ n) ∧
      L.family ⊆ M.family ∧
      (∀ i, (⟨Q.arity i, Q.factor i⟩ : AnySignature AlgebraicComplex) ∈ M.family) ∧
      Preprocessed M.family ∧ ¬ CommonOneSided M.family ∧
      Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M := by
  let e := Fintype.equivFin (Remaining a b)
  let g := Tensor.reindex e (C.contraction a b hab s f)
  have harity : Fintype.card (Remaining a b) + 2 = n := by
    simpa using remaining_card a b hab
  have hg : g ≠ 0 := by
    intro hz
    apply hcard
    funext x
    have h := congrFun hz (fun j => x (e.symm j))
    simpa only [g, Tensor.reindex_apply, Equiv.symm_apply_apply, Pi.zero_apply] using h
  have hgr : NetworkRealizable L.family g := (C.realizable a b hab s hf).reindex e
  obtain ⟨Q, hQ, hpos, hprime⟩ := exists_prime_decomposition g (by omega) hg
  obtain ⟨M, hsub, hmem, hfac, hpre, htwoM, hML, hLM⟩ :=
    adjoin_actual_prime_factors PG PR PF L hL htwo g (by omega) hg hgr Q hQ hpos hprime
  refine ⟨Q, M, ?_, ?_, hsub, hfac, hpre, htwoM, hML, hLM⟩
  · rw [hQ]
    exact Tensor.reindex_symm e _
  · intro i
    have hi := factor_arity_le Q i
    exact ⟨hpos i, hprime i, by omega⟩

end
end Paper2.HeightOne.PhaseCards
