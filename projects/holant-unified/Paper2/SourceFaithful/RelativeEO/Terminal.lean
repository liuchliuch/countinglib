import Paper2.SourceFaithful.RelativeEO.RealizedTerminal
import Paper2.RelativeEO.SeedARSRecovery
import Paper2.SourceFaithful.HighHeightCompleteSeed

/-! The complete relative EO terminal, with genuine strong descent on the
arity of actual graph outputs.  A finite equivalent language supplies exactly
the ARS factors of one smaller nonzero card.  Their actual attachments make a
literal seed; the smaller actual cards of that attached output are classified
by the induction hypothesis.  Single-seed recovery proves algebraic ARS, and
the independently established arbitrary-arity ARS terminal closes the case.
There is no saturation premise or assumed Paper 2 conclusion. -/
namespace Paper2.SourceFaithful.RelativeEO
open Tractable ExactInput Paper2.RelativeEO
open CommonPhase EndpointSelfLoop MatchingPropagation HighHeightNormalization

private theorem relative_terminal_arity
    (G : Paper1DirectGadgetAccepted) (O : Paper1OccurrenceAccepted)
    (Fac : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted)
    (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (B : Paper1BinaryInterpolationAccepted) (n : ℕ) :
    ∀ (L : Language), Preprocessed L.family → BothChargeSigns L.family →
      ¬ Tract (kImage L) → ∀ (f : Signature AlgebraicComplex n),
      0 < n → f ≠ 0 → Signature.CentralSupport f →
      NetworkRealizable L.family f → ¬ IsARSProduct f →
      FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro L hpre hboth hnot f hn hf he hgraph hout
    by_cases hsmall : n ≤ 4
    · exact realized_low_arity_relative_terminal G O Fac U E R B
        L hpre hboth hnot f hn hsmall hf he (NativeNetworkRealizesUpTo.of_realizable hgraph) hout
    have hn6 : 6 ≤ n := by
      obtain ⟨d,hd⟩ := even_arity_of_nonzero_central f hf he
      omega
    by_cases hhard : FixedFieldOutput.SharpPHard .nativeX L
    · exact hhard
    have heo : Tensor.ChargeLayer f 0 := (centralSupport_iff_chargeLayer f).mp he
    have heoC : Tensor.ChargeLayer (fun x => (f x : ℂ)) 0 := by
      intro x hx
      exact heo x (fun hzero => hx (by change (f x : ℂ) = 0; rw [hzero]; rfl))
    have hfC : (fun x => (f x : ℂ)) ≠ 0 := by
      intro hzero
      apply hf
      funext x
      exact Subtype.ext (congrFun hzero x)
    obtain ⟨r,hr⟩ := exists_nonzero_contraction (by simpa using (show 3 ≤ n by omega))
      (fun x => (f x : ℂ)) heoC hfC
    have hrCard : cardTable f r ≠ 0 :=
      (HighHeight.cardTable_nonzero_complex f r).mpr hr
    have hrcard := EndpointSelfLoop.remaining_card r.first r.second r.distinct
    have hrpos : 0 < Fintype.card (Remaining r.first r.second) := by
      simp only [Fintype.card_fin] at hrcard
      omega
    have hrlt : Fintype.card (Remaining r.first r.second) < n := by
      simp only [Fintype.card_fin] at hrcard
      omega
    have hrEO : Signature.CentralSupport (cardTable f r) :=
      (centralSupport_iff_chargeLayer _).mpr (HighHeight.cardTable_central f heo r)
    have hrARS : IsARSProduct (cardTable f r) := by
      by_contra hbad
      exact hhard (ih _ hrlt L hpre hboth hnot (cardTable f r) hrpos hrCard hrEO
        (cardTable_realizable f r hgraph) hbad)
    obtain ⟨N,P,z,c,hLN,hpreN,_,hNL,_,_,hz,_,_,hnewGraph,hnewEO,hseed⟩ :=
      HighHeight.normalize_single_card G Fac R L hpre (bothChargeSigns_not_oneSided hboth)
        f hgraph heo r hrpos hrCard hrARS
    have hbothN : BothChargeSigns N.family := by
      obtain ⟨⟨g,hg,x,hx,hneg⟩,⟨h,hh,y,hy,hpos⟩⟩ := hboth
      exact ⟨⟨g,hLN hg,x,hx,hneg⟩,⟨h,hLN hh,y,hy,hpos⟩⟩
    have hnotN : ¬ Tract (kImage N) :=
      fun ht => hnot (ht.mono_family (familyAction_mono sourceKBasis hLN))
    have hhardN : ¬ FixedFieldOutput.SharpPHard .nativeX N :=
      fun hh => hhard (hh.transport hNL)
    let ports : Fin P.count → Fin n := fun j => (P.ports (j,false)).val
    let g : Signature AlgebraicComplex n :=
      attachmentSequence ports (fun j => algebraicBinary (z j)) f
    have hgGraph : NetworkRealizable N.family g := hnewGraph
    have hgEO : Tensor.ChargeLayer g 0 := hnewEO
    have hgSeed : XAt (fun x => (g x : ℂ)) r := hseed
    have hgDeck : ARSDeck (fun x => (g x : ℂ)) := by
      intro e hcard
      have hcardAlg : cardTable g e ≠ 0 :=
        (HighHeight.cardTable_nonzero_complex g e).mpr hcard
      have hecard := EndpointSelfLoop.remaining_card e.first e.second e.distinct
      simp only [Fintype.card_fin] at hecard
      have hcardpos : 0 < Fintype.card (Remaining e.first e.second) := by omega
      have hcardlt : Fintype.card (Remaining e.first e.second) < n := by omega
      have hcardEO : Signature.CentralSupport (cardTable g e) :=
        (centralSupport_iff_chargeLayer _).mpr (HighHeight.cardTable_central g hgEO e)
      have hcardARS : IsARSProduct (cardTable g e) := by
        by_contra hbad
        exact hhardN (ih _ hcardlt N hpreN hbothN hnotN (cardTable g e)
          hcardpos hcardAlg hcardEO (cardTable_realizable g e hgGraph) hbad)
      exact HighHeight.ars_cardTable_ars g e hcardARS
    have hgARS : ProjectiveARS g := projectiveARS_of_seed_deck hn6 g hgEO r hgSeed hgDeck
    have hfARS : ProjectiveARS f :=
      (attachmentSequence_projectiveARS_iff ports z hz f).mp hgARS
    exact realized_ars_relative_terminal G O Fac U E R L hpre hboth hnot
      f hn hf he hfARS (NativeNetworkRealizesUpTo.of_realizable hgraph) hout

/-- Source Theorem 3.7 for every genuine positive EO gadget output over the
original mixed language, with the exact literal B_ARS exclusion. -/
theorem realized_relative_terminal
    (G : Paper1DirectGadgetAccepted) (O : Paper1OccurrenceAccepted)
    (Fac : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted)
    (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (B : Paper1BinaryInterpolationAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) {n : ℕ} (f : Signature AlgebraicComplex n)
    (hn : 0 < n) (hf : f ≠ 0) (he : Signature.CentralSupport f)
    (hgraph : NativeNetworkRealizesUpTo L.family f) (hout : ¬ IsARSProduct f) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨N,hN,_,hpreN,hbothN,hnotN,hNL⟩ :=
    retained_output G L hpre hboth hnot f hn hf hgraph
  have hmem : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ N.family := by
    rw [hN]
    exact Set.mem_insert _ _
  exact (relative_terminal_arity G O Fac U E R B n N hpreN hbothN hnotN
    f hn hf he (supplied_realizable hmem) hout).transport hNL

/-- The full relative-EO classification available to any finite retained stage.
Every conclusion concerns the actual graph output and the original problem. -/
theorem realized_isARSProduct
    (G : Paper1DirectGadgetAccepted) (O : Paper1OccurrenceAccepted)
    (Fac : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted)
    (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (B : Paper1BinaryInterpolationAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (hnohard : ¬ FixedFieldOutput.SharpPHard .nativeX L)
    {n : ℕ} (f : Signature AlgebraicComplex n) (hn : 0 < n) (hf : f ≠ 0)
    (he : Signature.CentralSupport f) (hgraph : NativeNetworkRealizesUpTo L.family f) :
    IsARSProduct f := by
  classical
  by_contra hout
  exact hnohard (realized_relative_terminal G O Fac U E R B L hpre hboth hnot
    f hn hf he hgraph hout)

/-- The literal-member formulation of source Theorem 3.7. -/
theorem relative_terminal
    (G : Paper1DirectGadgetAccepted) (O : Paper1OccurrenceAccepted)
    (Fac : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted)
    (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (B : Paper1BinaryInterpolationAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) {n : ℕ} (f : Signature AlgebraicComplex n)
    (he : Signature.CentralSupport f)
    (hmem : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hout : ¬ IsARSProduct f) : FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨hn,hf⟩ := hpre _ hmem
  exact realized_relative_terminal G O Fac U E R B L hpre hboth hnot f hn hf he
    (NativeNetworkRealizesUpTo.of_realizable (supplied_realizable hmem)) hout

end Paper2.SourceFaithful.RelativeEO
