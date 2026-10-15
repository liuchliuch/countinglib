import Paper2.SourceFaithful.SourceStatements.CyclicCardFactorBridge
import Paper2.HeightOne.Cyclic.Factorization
import Paper2.HeightOne.TensorPrimeTools
import Paper2.HeightOne.PhaseCards.Paper1Diagonal

/-! Literal source Theorem 5.22. Only the selected signature is assumed to have
even arity. Every card hypothesis refers to actual ordered prime factors of
the original native-X contraction, including both orientations and zero cards.
There is no whole-language evenness or preprocessing premise. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Paper2.SourceFaithful.SourceStatements.CyclicMinimumStatement
noncomputable section
open Tractable HeightOne HeightOne.Cyclic HeightOne.PhaseCards
open HeightOne.GroupSplit HeightOne.GroupSplit.MatrixGroup
open EndpointSelfLoop TypeParityStatement CyclicCardFactorBridge
open scoped BigOperators

/-- The full higher-arity original signature decomposes into actual ordered
binary factors. The proof reconstructs all coefficients, including its zero
entries, and then undoes the fixed Walsh change of coordinates. -/
theorem higher_binary_decomposition {N n : ℕ} (hN : 3 ≤ N)
    (R : Representatives .cyclic N) (f : Signature AlgebraicComplex n)
    (hf : f ≠ 0) (hn : 6 ≤ n) (hcards : CyclicCardFactors R f) :
    ∃ D : TensorDecomposition AlgebraicComplex n, D.value = f ∧
      ∀ i, D.arity i = 2 := by
  let : NeZero N := ⟨by omega⟩
  have hthree : ∃ s ∈ ({q : AlgebraicComplex | q ^ N = 1} : Set AlgebraicComplex),
      ∃ t ∈ ({q : AlgebraicComplex | q ^ N = 1} : Set AlgebraicComplex),
      ∃ u ∈ ({q : AlgebraicComplex | q ^ N = 1} : Set AlgebraicComplex),
      s ≠ t ∧ s ≠ u ∧ t ≠ u := by
    obtain ⟨s, hs, t, ht, u, hu, hst, hsu, htu⟩ := three_algebraic_root_phases N hN
    exact ⟨s, hs, t, ht, u, hu, hst, hsu, htu⟩
  have hm : ∀ a b (hab : a ≠ b), ∀ s : AlgebraicComplex, s ^ N = 1 →
      plusContraction a b hab s (walshCoordinates f) ≠ 0 →
      EqualityMatchingSupport (plusContraction a b hab s (walshCoordinates f)) := by
    intro a b hab s hs
    exact (root_card_data R f (by omega) hcards a b hab s hs).1
  have hp : ∀ a b (hab : a ≠ b), ∀ s : AlgebraicComplex, s ^ N = 1 →
      Product (Tensor.reindex (Fintype.equivFin (Remaining a b))
        (plusContraction a b hab s (walshCoordinates f))) := by
    intro a b hab s hs
    exact (root_card_data R f (by omega) hcards a b hab s hs).2
  obtain ⟨P, _hedges, hP⟩ := matching_core_of_cards (walshCoordinates f)
    (walsh_nonzero f hf) hn {q | q ^ N = 1} hthree hm hp
  have hc : 3 ≤ P.count := by
    have he := Matching.pair_count P
    omega
  have h0 := origin_nonzero_of_matching_cards (walshCoordinates f)
    (walsh_nonzero f hf) (by omega) {q | q ^ N = 1} hthree hm
  have hfactor : ∃ ρ : Fin P.count → AlgebraicComplex, (∀ i, ρ i ≠ 0) ∧
      ∀ t, walshCoordinates f (blockWord P t) = walshCoordinates f (fun _ => false) *
        ∏ i, (if t i then ρ i else 1) := by
    by_cases hcount : P.count = 3
    · obtain ⟨s, hs, t, ht, u, hu, hst, hsu, htu⟩ := three_algebraic_root_phases N hN
      apply logical_three_factorization (walshCoordinates f) P hcount hP h0 s t u hst hsu htu
      · intro a b hab q hq
        exact hm a b hab q (hq.elim (fun he => he ▸ hs)
          (fun hq => hq.elim (fun he => he ▸ ht) (fun he => he ▸ hu)))
      · intro a b hab q hq
        exact hp a b hab q (hq.elim (fun he => he ▸ hs)
          (fun hq => hq.elim (fun he => he ▸ ht) (fun he => he ▸ hu)))
    · exact logical_large_factorization provedDiagonalSlices (walshCoordinates f) P
        (by omega) hP h0 1 one_ne_zero
        (fun a b hab => hm a b hab 1 (one_pow N))
        (fun a b hab => hp a b hab 1 (one_pow N))
  obtain ⟨ρ, _hρ, hform⟩ := hfactor
  let Q := equalityDecomposition P (walshCoordinates f (fun _ => false)) h0 ρ
  have hQ : Q.value = walshCoordinates f :=
    decomposition_of_logical_product (walshCoordinates f) P hP h0 ρ hform
  refine ⟨Q.mapAction walsh, ?_, fun _ => rfl⟩
  rw [TensorDecomposition.value_mapAction, hQ]
  change walshBasis.action (walshCoordinates f) = f
  rw [← walshBasis_inverse_action, InvertibleKernel.action_symm_action]

/-- Exact source 5.22 conclusion from its original-signature and explicit
contraction-factor hypotheses. The surrounding minimum-language assumptions
are unnecessary for this local implication. -/
theorem source_5_22 {N n : ℕ} (hN : 3 ≤ N) (_hOdd : Odd N)
    (R : Representatives .cyclic N) (f : Signature AlgebraicComplex n)
    (heven : Even n) (hn : 2 < n) (hprime : TensorPrime f)
    (hcards : CyclicCardFactors R f) : n = 4 := by
  have hsmall : n < 6 := by
    by_contra h
    obtain ⟨D, hD, htwo⟩ := higher_binary_decomposition hN R f hprime.1 (by omega) hcards
    have hp := binary_decomposition_not_tensorPrime D htwo hn
    exact hp (hD.symm ▸ hprime)
  obtain ⟨r, hr⟩ := heven
  omega

end
end Paper2.SourceFaithful.SourceStatements.CyclicMinimumStatement

