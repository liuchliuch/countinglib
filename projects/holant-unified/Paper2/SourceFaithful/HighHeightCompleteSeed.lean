import Paper2.SourceFaithful.HighHeightCompleteCards
import Paper2.HighHeightNormalization.AlgebraicMountain

/-! A single real contraction card and its available algebraic binary factors
normalize an EO tensor in an arbitrary mixed ambient language.  This generic
seed route imposes no even-arity or charge-divisor promise on that ambient
language and is usable by the independent relative-EO induction. -/
namespace Paper2.SourceFaithful.HighHeight
set_option backward.isDefEq.respectTransparency false
open Tractable ExactInput Paper2.RelativeEO
open Paper2.HighHeightNormalization MatchingPropagation CommonPhase EndpointSelfLoop

theorem realized_ars_factors_access
    (G : Paper1DirectGadgetAccepted) (Fac : Paper1FactorClosureAccepted)
    (R : Paper1RestrictionAccepted) (L : Language)
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    {n : ℕ} (f : Signature AlgebraicComplex n) (hn : 0 < n) (hf : f ≠ 0)
    (hgraph : NetworkRealizable L.family f) (hars : IsARSProduct f) :
    ∃ (N : Language) (P : OrientedPerfectPairing n)
      (z : Fin P.count → AlgebraicComplex) (c : AlgebraicComplex),
      L.family ⊆ N.family ∧ Preprocessed N.family ∧ ¬ CommonOneSided N.family ∧
      FixedFieldOutput.Reduces .nativeX N L ∧ FixedFieldOutput.Reduces .nativeX L N ∧
      c ≠ 0 ∧ (∀ j, z j ≠ 0) ∧
      f = WeightedMatching.product P z (fun j => conjugateAlgebraic (z j)) c ∧
      (∀ j, AvailableBinary N (z j : ℂ)) := by
  obtain ⟨A,hA,hAL⟩ := G.adjoin_realizable L f hgraph
  have hLA : L.family ⊆ A.family := by rw [hA]; exact Set.subset_insert _ _
  have hpreA : Preprocessed A.family := by
    rw [hA]
    exact Paper2.HeightThree.insert_nonzero_positive_preprocessed _ _ hn hf hpre
  have htwoA : ¬ CommonOneSided A.family := by
    intro hs
    apply htwo
    rcases hs with hs | hs
    · exact Or.inl (fun g hg => hs g (hLA hg))
    · exact Or.inr (fun g hg => hs g (hLA hg))
  have hmemA : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ A.family := by
    rw [hA]
    exact Set.mem_insert _ _
  obtain ⟨P,z,c,N,hc,hz,hform,_,hAN,hfac,hpreN,htwoN,_,_,_,_,hNA,hAN'⟩ :=
    ars_factors_retained Fac R A hpreA htwoA f hmemA hars
  refine ⟨N,P,z,c,(fun _ h => hAN (hLA h)),hpreN,htwoN,hNA.trans hAL,
    (R.restriction_2_5 L A hLA).trans hAN',hc,hz,hform,?_⟩
  intro j
  refine ⟨z j,rfl,?_⟩
  rw [binaryTable_eoSignature]
  exact supplied_realizable (hfac j)

theorem cardTable_central {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : Tensor.ChargeLayer f 0) (e : PortPair (Fin n)) :
    Tensor.ChargeLayer (cardTable f e) 0 :=
  Tensor.reindex_chargeLayer _
    (Tensor.contractX_chargeLayer (Tensor.reindex_chargeLayer (splitPorts e.first e.second e.distinct) hf))

/-- An actual selected seed card is normalized by precisely its own ordered
algebraic factors.  The result is a genuine graph over a finite equivalent
language, not a free transformed EO table. -/
theorem normalize_single_card
    (G : Paper1DirectGadgetAccepted) (Fac : Paper1FactorClosureAccepted)
    (R : Paper1RestrictionAccepted) (L : Language)
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    {n : ℕ} (f : Signature AlgebraicComplex n)
    (hgraph : NetworkRealizable L.family f) (hf : Tensor.ChargeLayer f 0)
    (e : PortPair (Fin n)) (hn : 0 < Fintype.card (Remaining e.first e.second))
    (he : cardTable f e ≠ 0) (hars : IsARSProduct (cardTable f e)) :
    ∃ (N : Language) (P : Matching (Remaining e.first e.second))
      (z : Fin P.count → AlgebraicComplex) (c : AlgebraicComplex),
      L.family ⊆ N.family ∧ Preprocessed N.family ∧ ¬ CommonOneSided N.family ∧
      FixedFieldOutput.Reduces .nativeX N L ∧ FixedFieldOutput.Reduces .nativeX L N ∧
      c ≠ 0 ∧ (∀ j, z j ≠ 0) ∧
      contraction (fun x => (f x : ℂ)) e =
        product P (fun j => (z j : ℂ)) (fun j => star (z j : ℂ)) (c : ℂ) ∧
      (∀ j, AvailableBinary N (z j : ℂ)) ∧
      NetworkRealizable N.family
        (attachmentSequence (fun j => (P.ports (j,false)).val) (fun j => algebraicBinary (z j)) f) ∧
      Tensor.ChargeLayer
        (attachmentSequence (fun j => (P.ports (j,false)).val) (fun j => algebraicBinary (z j)) f) 0 ∧
      XAt (fun x => (attachmentSequence (K := AlgebraicComplex) (fun j => (P.ports (j,false)).val)
        (fun j => algebraicBinary (z j)) f x : ℂ)) e := by
  obtain ⟨N,P,z,c,hLN,hpreN,htwoN,hNL,hLN',hc,hz,hform,ha⟩ :=
    realized_ars_factors_access G Fac R L hpre htwo (cardTable f e) hn he
      (cardTable_realizable f e hgraph) hars
  let W := cardWitness_of_ordered f e P z c hc hz hform ha
  refine ⟨N,W.pairing,W.parameter,W.scalar,hLN,hpreN,htwoN,hNL,hLN',
    W.scalar_ne_zero,W.parameter_ne_zero,W.coefficient,W.available,?_,?_,?_⟩
  · apply attachmentSequence_realizable _ _ _ (realizable_mono hLN hgraph)
    intro j
    obtain ⟨a,ha,hr⟩ := W.available j
    have haa : a = W.parameter j := Subtype.ext ha
    simpa only [haa] using hr
  · exact attachmentSequence_central _ _ f hf
  · rw [attachmentSequence_coe]
    exact normalize_selected_loop_isX (fun x => (f x : ℂ)) e W.pairing
      (fun j => (W.parameter j : ℂ)) (W.scalar : ℂ)
      (by exact_mod_cast W.scalar_ne_zero) (fun j => by exact_mod_cast W.parameter_ne_zero j)
      W.coefficient

end Paper2.SourceFaithful.HighHeight
