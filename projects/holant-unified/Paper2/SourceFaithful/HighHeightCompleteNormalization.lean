import Paper2.SourceFaithful.HighHeightCompleteCards
import Paper2.HighHeightNormalization.AlgebraicMountain

/-! The finite-language assembly of Lemma 8.5.  The independent remaining
relative-EO terminal is exposed precisely as classification of actual small
boundary graphs in retained equivalent languages.  No central tensor is
adjoined and no normalization conclusion is accepted as a parameter. -/
namespace Paper2.SourceFaithful.HighHeight
open Tractable ExactInput Paper2.RelativeEO
open Paper2.HighHeightNormalization MatchingPropagation CommonPhase EndpointSelfLoop

structure NormalizedMountain (L : Language) (d : ℕ) where
  stage : RetainedStage L d
  mountain : Signature AlgebraicComplex (2*d)
  central : Signature AlgebraicComplex (2*d)
  leftEndpoint : AlgebraicComplex
  rightEndpoint : AlgebraicComplex
  endpoint_ne_zero : leftEndpoint * rightEndpoint ≠ 0
  central_eo : Tensor.ChargeLayer central 0
  central_ne_zero : central ≠ 0
  decomposition : mountain = algebraicMountain leftEndpoint rightEndpoint central
  member : (⟨2*d,mountain⟩ : AnySignature AlgebraicComplex) ∈ stage.language.family
  coefficient : PortPair (Fin (2*d)) → ℂ
  matching : (e : PortPair (Fin (2*d))) → Matching (Remaining e.first e.second)
  deck : MatchingDeck (fun x => (central x : ℂ)) coefficient matching
  coefficient_ne_zero : ∀ e, coefficient e ≠ 0

/-- The complete normalization construction consumes only ARS membership of
nonzero actual outputs on fewer than 2d boundary ports, at the finite stages
it constructs.  A full relative-EO terminal under no-hardness discharges this
premise separately. -/
theorem finite_port_normalization
    (G : Paper1DirectGadgetAccepted) (Fac : Paper1FactorClosureAccepted)
    (R : Paper1RestrictionAccepted) (L : Language) {d : ℕ} (hd : 4 ≤ d)
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (heven : ∀ g ∈ L.family, Even g.1)
    (hdiv : ∀ g ∈ L.family, Tensor.HalfChargeDivisible g.2 d)
    (hsmall : ∀ S : RetainedStage L d, ∀ {n : ℕ}
      (f : Signature AlgebraicComplex n), 0 < n → n < 2*d →
      NetworkRealizable S.language.family f → f ≠ 0 → IsARSProduct f)
    (M F : Signature AlgebraicComplex (2*d)) (a b : AlgebraicComplex)
    (hab : a*b ≠ 0) (hF : Tensor.ChargeLayer F 0) (hFn : F ≠ 0)
    (hM : M = algebraicMountain a b F)
    (hmem : (⟨2*d,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Nonempty (NormalizedMountain L d) := by
  classical
  have hn : 8 ≤ Fintype.card (Fin (2*d)) := by simpa using (show 8 ≤ 2*d by omega)
  have hreal : NetworkRealizable L.family M := supplied_realizable hmem
  let I := RetainedStage.refl R L d hpre heven hdiv
  obtain ⟨r,hr⟩ := exists_nonzero_contraction (by omega : 3 ≤ Fintype.card (Fin (2*d)))
    (fun x => (F x : ℂ)) ((coe_chargeLayer _ _).mpr hF) ((coe_tensor_nonzero _).mpr hFn)
  have hrcard : cardTable M r ≠ 0 := by
    apply (cardTable_nonzero_complex M r).mpr
    rw [hM,algebraicMountain_loop]
    exact hr
  have hroom (e : PortPair (Fin (2*d))) :
      0 < Fintype.card (Remaining e.first e.second) ∧
      Fintype.card (Remaining e.first e.second) < 2*d := by
    have h := cardTable_arity e
    omega
  have hrsars : IsARSProduct (cardTable M r) :=
    hsmall I _ (hroom r).1 (hroom r).2 (cardTable_realizable M r hreal) hrcard
  obtain ⟨S₀,⟨W⟩⟩ := contraction_factors_stage G Fac R L hpre htwo heven hdiv
    M hreal r (hroom r).1 hrcard hrsars
  let p₀ : Fin W.pairing.count → Fin (2*d) := fun j => (W.pairing.ports (j,false)).val
  let F₀ := attachmentSequence p₀ (fun j => algebraicBinary (W.parameter j)) F
  let M₀ := attachmentSequence p₀ (fun j => algebraicBinary (W.parameter j)) M
  let a₀ := (∏ j,conjugateAlgebraic (W.parameter j))*a
  let b₀ := (∏ j,W.parameter j)*b
  have hprod₀ : (∏ j,W.parameter j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => W.parameter_ne_zero j)
  have hprod₀' : (∏ j,conjugateAlgebraic (W.parameter j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => conjugateAlgebraic_ne_zero.mpr (W.parameter_ne_zero j))
  have hab₀ : a₀*b₀ ≠ 0 := mul_ne_zero
    (mul_ne_zero hprod₀' (left_ne_zero_of_mul hab))
    (mul_ne_zero hprod₀ (right_ne_zero_of_mul hab))
  have hF₀ : Tensor.ChargeLayer F₀ 0 := attachmentSequence_central _ _ F hF
  have hFn₀ : F₀ ≠ 0 := attachmentSequence_nonzero _ _ W.parameter_ne_zero F hFn
  have hM₀ : M₀ = algebraicMountain a₀ b₀ F₀ := by
    dsimp [M₀,F₀,a₀,b₀]
    exact (congrArg (attachmentSequence p₀ (fun j => algebraicBinary (W.parameter j))) hM).trans
      (attachmentSequence_algebraicMountain _ _ _ _ _)
  have hreal₀ : NetworkRealizable S₀.language.family M₀ := by
    apply attachmentSequence_realizable _ _ _ (realizable_mono S₀.contains hreal)
    intro j
    obtain ⟨z,hz,hrealz⟩ := W.available j
    have hza : z = W.parameter j := Subtype.ext hz
    simpa only [hza] using hrealz
  have hseed : contraction (fun x => (F x : ℂ)) r = product W.pairing
      (fun j => (W.parameter j : ℂ)) (fun j => star (W.parameter j : ℂ)) (W.scalar : ℂ) := by
    have hloop : contraction (fun x => (M x : ℂ)) r = contraction (fun x => (F x : ℂ)) r := by
      rw [hM,algebraicMountain_loop]
    exact hloop.symm.trans W.coefficient
  have hX₀ : XAt (fun x => (F₀ x : ℂ)) r := by
    rw [show (fun x => (F₀ x : ℂ)) =
      attachFamily p₀ (fun j => (W.parameter j : ℂ)) (fun x => (F x : ℂ)) from
      attachmentSequence_coe _ _ _]
    exact normalize_selected_loop_isX (fun x => (F x : ℂ)) r W.pairing
      (fun j => (W.parameter j : ℂ)) (W.scalar : ℂ)
      (by exact_mod_cast W.scalar_ne_zero) (fun j => by exact_mod_cast W.parameter_ne_zero j) hseed
  have hcards₀ : ∀ e, cardTable M₀ e ≠ 0 → IsARSProduct (cardTable M₀ e) := by
    intro e he
    exact hsmall S₀ _ (hroom e).1 (hroom e).2 (cardTable_realizable M₀ e hreal₀) he
  obtain ⟨T₁,hT₁⟩ := finite_contraction_factors_stage G Fac R S₀.language S₀.preprocessed
    (S₀.not_oneSided htwo) S₀.even S₀.divisible M₀ hreal₀ Finset.univ
    (fun e _ => (hroom e).1) (fun e _ => hcards₀ e)
  let S₁ := S₀.trans T₁
  have hcardsF₀ : ∀ e, contraction (fun x => (F₀ x : ℂ)) e ≠ 0 →
      ∃ (P : Matching (Remaining e.first e.second)) (z : Fin P.count → ℂ) (c : ℂ),
        c ≠ 0 ∧ (∀ j, z j ≠ 0) ∧ (∀ j, AvailableBinary S₁.language (z j)) ∧
        contraction (fun x => (F₀ x : ℂ)) e = product P z (fun j => star (z j)) c := by
    intro e he
    have hcard : cardTable M₀ e ≠ 0 := by
      apply (cardTable_nonzero_complex M₀ e).mpr
      rw [hM₀,algebraicMountain_loop]
      exact he
    obtain ⟨C⟩ := hT₁ e (Finset.mem_univ _) hcard
    refine ⟨C.pairing,(fun j => (C.parameter j : ℂ)),(C.scalar : ℂ),?_,?_,C.available,?_⟩
    · exact_mod_cast C.scalar_ne_zero
    · intro j
      change (C.parameter j : ℂ) ≠ 0
      exact_mod_cast C.parameter_ne_zero j
    · have hloop : contraction (fun x => (M₀ x : ℂ)) e =
          contraction (fun x => (F₀ x : ℂ)) e := by
        rw [hM₀,algebraicMountain_loop]
      exact hloop.symm.trans C.coefficient
  obtain ⟨m,p,z,hm,hz,hAz,hcond⟩ := normalize_seed_finite_access hn
    (AvailableBinary S₁.language) (availableBinary_star S₁.language) _ r hX₀ hcardsF₀
  choose zA hzA hrealA using hAz
  have hzA' : ∀ j, zA j ≠ 0 := by
    intro j h
    apply hz j
    rw [← hzA j,h]
    rfl
  let F₁ := attachmentSequence p (fun j => algebraicBinary (zA j)) F₀
  let M₁ := attachmentSequence p (fun j => algebraicBinary (zA j)) M₀
  let a₁ := (∏ j,conjugateAlgebraic (zA j))*a₀
  let b₁ := (∏ j,zA j)*b₀
  have hprod₁ : (∏ j,zA j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hzA' j)
  have hprod₁' : (∏ j,conjugateAlgebraic (zA j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => conjugateAlgebraic_ne_zero.mpr (hzA' j))
  have hab₁ : a₁*b₁ ≠ 0 := mul_ne_zero
    (mul_ne_zero hprod₁' (left_ne_zero_of_mul hab₀))
    (mul_ne_zero hprod₁ (right_ne_zero_of_mul hab₀))
  have hF₁ : Tensor.ChargeLayer F₁ 0 := attachmentSequence_central _ _ F₀ hF₀
  have hFn₁ : F₁ ≠ 0 := attachmentSequence_nonzero _ _ hzA' F₀ hFn₀
  have hM₁ : M₁ = algebraicMountain a₁ b₁ F₁ := by
    dsimp [M₁,F₁,a₁,b₁]
    rw [hM₀]
    exact attachmentSequence_algebraicMountain _ _ _ _ _
  have hreal₁ : NetworkRealizable S₁.language.family M₁ :=
    attachmentSequence_realizable _ _ _ (realizable_mono T₁.contains hreal₀) hrealA
  have hcond₁ : (∀ e, r.Disjoint e → XAt (fun x => (F₁ x : ℂ)) e) ∨
      SecondCondition (fun x => (F₁ x : ℂ)) r := by
    have hcoe : (fun x => (F₁ x : ℂ)) = attachFamily p z (fun x => (F₀ x : ℂ)) := by
      rw [show (fun x => (F₁ x : ℂ)) =
        attachFamily p (fun j => (zA j : ℂ)) (fun x => (F₀ x : ℂ)) from
        attachmentSequence_coe _ _ _]
      have hza : (fun j => (zA j : ℂ)) = z := funext hzA
      rw [hza]
    rw [hcoe]
    exact hcond
  have hdeckARS : ARSDeck (fun x => (F₁ x : ℂ)) := by
    intro e he
    have hcard : cardTable M₁ e ≠ 0 := by
      apply (cardTable_nonzero_complex M₁ e).mpr
      rw [hM₁,algebraicMountain_loop]
      exact he
    have h := ars_cardTable_ars M₁ e
      (hsmall S₁ _ (hroom e).1 (hroom e).2 (cardTable_realizable M₁ e hreal₁) hcard)
    rw [hM₁,algebraicMountain_loop] at h
    exact h
  obtain ⟨lam,P,hdeck,hnz⟩ := x_line_matching_deck hn _ hdeckARS r hcond₁
  obtain ⟨N,hN,hNS₁⟩ := G.adjoin_realizable S₁.language M₁ hreal₁
  have hS₁N : S₁.language.family ⊆ N.family := by rw [hN]; exact Set.subset_insert _ _
  have hmountain : IsMountain M₁ := by
    rw [hM₁]
    exact algebraicMountain_isMountain (by omega) a₁ b₁ hab₁ F₁ hF₁
  have hM₁nz : M₁ ≠ 0 := by
    intro h
    exact hmountain.zero_ne_zero (congrFun h _)
  have hM₁div : Tensor.HalfChargeDivisible M₁ d := by
    obtain ⟨V,hU,hX,hV⟩ := hreal₁.ordered
    rw [← hV]
    exact V.denote_halfChargeDivisible (even_two_mul d)
      (fun v => S₁.even _ (hU v)) hX d (fun v => S₁.divisible _ (hU v))
  let T₂ : RetainedStage S₁.language d := {
    language := N
    contains := hS₁N
    preprocessed := by
      rw [hN]
      exact Paper2.HeightThree.insert_nonzero_positive_preprocessed _ _ (by change 0 < 2*d; omega)
        hM₁nz S₁.preprocessed
    even := by
      intro g hg
      rw [hN] at hg
      rcases hg with rfl | hg
      · exact even_two_mul d
      · exact S₁.even g hg
    divisible := by
      intro g hg
      rw [hN] at hg
      rcases hg with rfl | hg
      · exact hM₁div
      · exact S₁.divisible g hg
    backward := hNS₁
    forward := R.restriction_2_5 S₁.language N hS₁N }
  refine ⟨⟨S₁.trans T₂,M₁,F₁,a₁,b₁,hab₁,hF₁,hFn₁,hM₁,?_,lam,P,hdeck,hnz⟩⟩
  change (⟨2*d,M₁⟩ : AnySignature AlgebraicComplex) ∈ N.family
  rw [hN]
  exact Set.mem_insert _ _

end Paper2.SourceFaithful.HighHeight
