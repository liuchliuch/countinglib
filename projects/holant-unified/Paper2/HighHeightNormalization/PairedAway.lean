import Paper2.HighHeightNormalization.PortFactor

/-! Lemma 8.5, the case in which every card away from the seed pair retains
that pair as a matching edge. All comparisons are actual double sums. -/
namespace Paper2.HighHeightNormalization
open MatchingPropagation CommonPhase EndpointSelfLoop
variable {ι : Type}

/-- The ratio of the retained binary factor agrees between disjoint cards.
Nonvanishing of their comparison is proved from the literal loop sum. -/
theorem paired_away_ratio (F : Tensor ℂ ι) (r e s : PortPair ι)
    (her : e.Disjoint r) (hsr : s.Disjoint r) (hes : e.Disjoint s)
    (P : Matching (Remaining e.first e.second))
    (Q : Matching (Remaining s.first s.second)) (z w c d : ℂ)
    (hz : z ≠ 0) (hc : c ≠ 0)
    (he : contraction F e = fun x =>
      phaseWeight z (x (e.residual r her).first) * c * literal P ℂ x)
    (hs : contraction F s = fun x =>
      phaseWeight w (x (s.residual r hsr).first) * d * literal Q ℂ x) :
    star z * w = z * star w := by
  let H : Tensor ℂ ι := fun x => c *
    (e.residual s hes).pairSum (literal P ℂ) (restrict e.first e.second x)
  let J : Tensor ℂ ι := fun x => d *
    (s.residual e hes.symm).pairSum (literal Q ℂ) (restrict s.first s.second x)
  have hH : ∀ x, H (fun i => !(x i)) = H x := by
    intro x
    change c * (e.residual s hes).pairSum (literal P ℂ)
      (fun a => !(restrict e.first e.second x a)) = _
    rw [pairSum_literal_complement]
  have hJ : ∀ x, J (fun i => !(x i)) = J x := by
    intro x
    change d * (s.residual e hes.symm).pairSum (literal Q ℂ)
      (fun a => !(restrict s.first s.second x a)) = _
    rw [pairSum_literal_complement]
  have her' := residual_disjoint e r s her hes hsr.symm
  have hsr' := residual_disjoint s r e hsr hes.symm her.symm
  have heq : ∀ x, phaseWeight z (x r.first) * H x = phaseWeight w (x r.first) * J x := by
    intro x
    have h := double_loop_eq F e s hes x
    rw [he,hs,pairSum_phase P _ z c _ her'.1 her'.2.1,
      pairSum_phase Q _ w d _ hsr'.1 hsr'.2.1] at h
    exact h
  have hnz : ∃ x, phaseWeight z (x r.first) * H x ≠ 0 := by
    obtain ⟨y,hy⟩ := pairSum_isX_nonzero (e.residual s hes)
      (show IsX (literal P ℂ) from ⟨P,1,one_ne_zero,by funext x; simp⟩)
    let x := extendPair e.first e.second e.distinct y false
    refine ⟨x,mul_ne_zero (phaseWeight_ne_zero hz _) ?_⟩
    dsimp [H,x]
    rw [PortPair.restrict_extend]
    exact mul_ne_zero hc hy
  exact phase_ratio_of_equal r.first z w H J hH hJ heq hnz

/-- One actual one-port binary attachment normalizes every away card. The
factor is selected from an actual card, and connectedness uses an explicit
pair avoiding the seed, the current card, and the reference card. -/
theorem normalize_paired_away [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (r : PortPair ι) (hr : XAt F r)
    (hcards : ∀ e (her : e.Disjoint r),
      ∃ (P : Matching (Remaining e.first e.second)) (z : Fin P.count → ℂ) (c : ℂ),
        c ≠ 0 ∧ (∀ j, z j ≠ 0) ∧
        contraction F e = product P z (fun j => star (z j)) c ∧
        mate P (e.residual r her).first = (e.residual r her).second) :
    ∃ z : ℂ, z ≠ 0 ∧ ∀ e, r.Disjoint e → XAt (attach r.first (binary z) F) e := by
  classical
  have hforms : ∀ e (her : e.Disjoint r),
      ∃ (P : Matching (Remaining e.first e.second)) (z c : ℂ),
        z ≠ 0 ∧ c ≠ 0 ∧ contraction F e = fun x =>
          phaseWeight z (x (e.residual r her).first) * c * literal P ℂ x := by
    intro e her
    obtain ⟨P,z,c,hc,hz,he,hm⟩ := hcards e her
    obtain ⟨w,C,hw,hC,_,hform⟩ := paired_card_form F e r her hr P z c hc hz he hm
    exact ⟨P,w,C,hw,hC,hform⟩
  choose P z c hz hc hform using hforms
  obtain ⟨s,hrs,_⟩ := PortPair.exists_common_disjoint (by omega) r r
  let w := z s hrs.symm
  refine ⟨w,hz s hrs.symm,?_⟩
  intro e hre
  obtain ⟨t,hrt,het,hst⟩ := exists_disjoint_three hn r e s
  have hstRatio := paired_away_ratio F r s t hrs.symm hrt.symm hst
    (P s hrs.symm) (P t hrt.symm) (z s hrs.symm) (z t hrt.symm)
    (c s hrs.symm) (c t hrt.symm) (hz s hrs.symm) (hc s hrs.symm)
    (hform s hrs.symm) (hform t hrt.symm)
  have hteRatio := paired_away_ratio F r t e hrt.symm hre.symm het.symm
    (P t hrt.symm) (P e hre.symm) (z t hrt.symm) (z e hre.symm)
    (c t hrt.symm) (c e hre.symm) (hz t hrt.symm) (hc t hrt.symm)
    (hform t hrt.symm) (hform e hre.symm)
  have hratio := phase_ratio_trans (hz t hrt.symm) hstRatio hteRatio
  have heq : contraction (attach r.first (binary w) F) e =
      attach (e.residual r hre.symm).first (binary w) (contraction F e) := by
    funext x
    change (∑ b : Bool, attach r.first (binary w) F
      (extendPair e.first e.second e.distinct x b)) = _
    simp only [attach_binary,extend_other e x _ r.first hre.1 hre.2.1]
    rw [← Finset.mul_sum]
    rfl
  rw [XAt,heq,hform e hre.symm]
  exact attach_phase_isX (P e hre.symm) _ w (z e hre.symm) (c e hre.symm)
    (hz s hrs.symm) (hz e hre.symm) (hc e hre.symm) hratio

/-- Closing the paired-away branch uses only the new actual weighted deck;
its zero cards are still allowed and are removed by Lemma 8.4 itself. -/
theorem paired_away_full_deck [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (r : PortPair ι) (hr : XAt F r)
    (hcards : ∀ e (her : e.Disjoint r),
      ∃ (P : Matching (Remaining e.first e.second)) (z : Fin P.count → ℂ) (c : ℂ),
        c ≠ 0 ∧ (∀ j, z j ≠ 0) ∧
        contraction F e = product P z (fun j => star (z j)) c ∧
        mate P (e.residual r her).first = (e.residual r her).second)
    (hstage : ∀ z, z ≠ 0 → WeightedDeck (attach r.first (binary z) F)) :
    ∃ z : ℂ, z ≠ 0 ∧ ∀ e, XAt (attach r.first (binary z) F) e := by
  obtain ⟨z,hz,haway⟩ := normalize_paired_away hn F r hr hcards
  exact ⟨z,hz,propagation_condition_one hn _ (hstage z hz) r haway⟩

end Paper2.HighHeightNormalization
