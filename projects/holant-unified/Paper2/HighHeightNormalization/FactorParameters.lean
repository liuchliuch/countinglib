import Paper2.HighHeightNormalization.SeedFinish

/-! The normalizing parameters are selected from the actual ordered ARS
factors, possibly with their two ports reversed.  This additional bookkeeping
allows the finite-language construction to use supplied binary signatures
rather than arbitrary complex witnesses. -/
namespace Paper2.HighHeightNormalization
open MatchingPropagation CommonPhase EndpointSelfLoop
variable {ι : Type}

/-- The two exceptional parameters are literal entries of their respective
ordered factors, with the conjugate entry used exactly when the port is the
second endpoint of that factor. -/
theorem product_two_phase_parameters (P : Matching ι) (z : Fin P.count → ℂ) (c : ℂ)
    (hc : c ≠ 0) (hz : ∀ i, z i ≠ 0)
    (a b : ι) (hi : (P.ports.symm a).1 ≠ (P.ports.symm b).1)
    (hother : ∀ i, i ≠ (P.ports.symm a).1 → i ≠ (P.ports.symm b).1 → z i = star (z i)) :
    ∃ w v C : ℂ, w ≠ 0 ∧ v ≠ 0 ∧ C ≠ 0 ∧
      (w = z (P.ports.symm a).1 ∨ w = star (z (P.ports.symm a).1)) ∧
      (v = z (P.ports.symm b).1 ∨ v = star (z (P.ports.symm b).1)) ∧
      product P z (fun i => star (z i)) c =
        fun x => phaseWeight w (x a) * phaseWeight v (x b) * C * literal P ℂ x := by
  classical
  let j := (P.ports.symm a).1
  let k := (P.ports.symm b).1
  let s := (P.ports.symm a).2
  let t := (P.ports.symm b).2
  let w := if s then star (z j) else z j
  let v := if t then star (z k) else z k
  let C := c * ∏ i ∈ (Finset.univ.erase j).erase k, z i
  refine ⟨w,v,C,?_,?_,?_,?_,?_,?_⟩
  · dsimp [w]; cases s <;> simpa using hz j
  · dsimp [v]; cases t <;> simpa using hz k
  · exact mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun i _ => hz i))
  · dsimp [w]; cases s
    · exact Or.inl rfl
    · exact Or.inr rfl
  · dsimp [v]; cases t
    · exact Or.inl rfl
    · exact Or.inr rfl
  · funext x
    rw [product_two P z (fun i => star (z i)) c j k hi s t hother]
    have ha : P.ports (j,s) = a := P.ports.apply_symm_apply a
    have hb : P.ports (k,t) = b := P.ports.apply_symm_apply b
    rw [ha,hb]
    have h₁ : (if x a = s then z j else star (z j)) = phaseWeight w (x a) := by
      dsimp [w,phaseWeight]; cases s <;> cases x a <;> simp
    have h₂ : (if x b = t then z k else star (z k)) = phaseWeight v (x b) := by
      dsimp [v,phaseWeight]; cases t <;> cases x b <;> simp
    rw [h₁,h₂]

/-- The distinct-mates normalization selects both attaching binaries from
the factors of one actual nonzero card.  A predicate records access to these
binary tables and is required to be closed only under reversal. -/
theorem normalize_distinct_mates_access (A : ℂ → Prop)
    (hAstar : ∀ z, A z → A (star z))
    (F : Tensor ℂ ι) (r s : PortPair ι) (hrs : r.Disjoint s) (hr : XAt F r)
    (P : Matching (Remaining s.first s.second)) (z : Fin P.count → ℂ) (c : ℂ)
    (hc : c ≠ 0) (hz : ∀ i, z i ≠ 0) (hAz : ∀ i, A (z i))
    (hs : contraction F s = product P z (fun i => star (z i)) c)
    (hm : mate P (s.residual r hrs.symm).first ≠ (s.residual r hrs.symm).second) :
    ∃ w v : ℂ, w ≠ 0 ∧ v ≠ 0 ∧ A w ∧ A v ∧
      SecondCondition (attach r.first (binary w) (attach r.second (binary v) F)) r := by
  have hi : (P.ports.symm (s.residual r hrs.symm).first).1 ≠
      (P.ports.symm (s.residual r hrs.symm).second).1 := by
    intro he
    exact hm (mate_of_same_index P _ _ (s.residual r hrs.symm).distinct he)
  have hother : ∀ i, i ≠ (P.ports.symm (s.residual r hrs.symm).first).1 →
      i ≠ (P.ports.symm (s.residual r hrs.symm).second).1 → z i = star (z i) := by
    intro i hi hj
    exact factor_eq_of_disjoint_X F s r hrs.symm hr P z (fun i => star (z i)) c hz
      (fun i => by simpa using hz i) hs i ((avoids_iff_index P i _).mpr ⟨hi,hj⟩)
  obtain ⟨w,v,C,hw,hv,hC,hwz,hvz,hprod⟩ :=
    product_two_phase_parameters P z c hc hz _ _ hi hother
  have hAw : A w := by
    rcases hwz with h | h
    · rw [h]; exact hAz _
    · rw [h]; exact hAstar _ (hAz _)
  have hAv : A v := by
    rcases hvz with h | h
    · rw [h]; exact hAz _
    · rw [h]; exact hAstar _ (hAz _)
  have hform := hs.trans hprod
  have hflat := (double_comparison F s r hrs.symm hr).2
  rw [hform] at hflat
  have hratio := two_phase_ratio P (s.residual r hrs.symm) hm w v C hw hv hC hflat
  refine ⟨w,v,hw,hv,hAw,hAv,?_,s,hrs,P,(w * star w) * (v * star v) * C,?_,?_,hm⟩
  · obtain ⟨Q,d,hd,hQ⟩ := hr
    refine ⟨Q,(star w * v) * d,mul_ne_zero (mul_ne_zero (by simpa using hw) hv) hd,?_⟩
    rw [two_attachments_loop F r w v hratio,hQ]
    funext x
    ring
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hw (by simpa using hw))
      (mul_ne_zero hv (by simpa using hv))) hC
  · have heq : contraction (attach r.first (binary w) (attach r.second (binary v) F)) s =
        attach (s.residual r hrs.symm).first (binary w)
          (attach (s.residual r hrs.symm).second (binary v) (contraction F s)) := by
      change contraction (attach (s.residual r hrs.symm).first.val (binary w)
        (attach (s.residual r hrs.symm).second.val (binary v) F)) s = _
      rw [contraction_attach_away _ s (s.residual r hrs.symm).first w,
        contraction_attach_away _ s (s.residual r hrs.symm).second v]
    rw [heq,hform]
    exact two_phase_mating_eq P _ _ w v C

/-- A single accessible binary, selected from one of the actual away cards,
normalizes every away contraction.  All scalar and phase comparisons are the
same actual double-contraction identities used by the original proof. -/
theorem normalize_paired_away_access [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (A : ℂ → Prop) (hAstar : ∀ z, A z → A (star z))
    (F : Tensor ℂ ι) (r : PortPair ι) (hr : XAt F r)
    (hcards : ∀ e (her : e.Disjoint r),
      ∃ (P : Matching (Remaining e.first e.second)) (z : Fin P.count → ℂ) (c : ℂ),
        c ≠ 0 ∧ (∀ j, z j ≠ 0) ∧ (∀ j, A (z j)) ∧
        contraction F e = product P z (fun j => star (z j)) c ∧
        mate P (e.residual r her).first = (e.residual r her).second) :
    ∃ z : ℂ, z ≠ 0 ∧ A z ∧ ∀ e, r.Disjoint e → XAt (attach r.first (binary z) F) e := by
  classical
  have hforms : ∀ e (her : e.Disjoint r),
      ∃ (P : Matching (Remaining e.first e.second)) (z c : ℂ),
        z ≠ 0 ∧ c ≠ 0 ∧ A z ∧ contraction F e = fun x =>
          phaseWeight z (x (e.residual r her).first) * c * literal P ℂ x := by
    intro e her
    obtain ⟨P,z,c,hc,hz,hAz,he,hm⟩ := hcards e her
    obtain ⟨w,C,hw,hC,hwz,hform⟩ := paired_card_form F e r her hr P z c hc hz he hm
    have hAw : A w := by
      rcases hwz with h | h
      · rw [h]; exact hAz _
      · rw [h]; exact hAstar _ (hAz _)
    exact ⟨P,w,C,hw,hC,hAw,hform⟩
  choose P z c hz hc hAz hform using hforms
  obtain ⟨s,hrs,_⟩ := PortPair.exists_common_disjoint (by omega) r r
  let w := z s hrs.symm
  refine ⟨w,hz s hrs.symm,hAz s hrs.symm,?_⟩
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

/-- The complete seed case split now retains access to every selected
attaching binary.  No new binary representative is manufactured. -/
theorem normalize_seed_finite_access [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (A : ℂ → Prop) (hAstar : ∀ z, A z → A (star z))
    (F : Tensor ℂ ι) (r : PortPair ι) (hr : XAt F r)
    (hcards : ∀ e, contraction F e ≠ 0 →
      ∃ (P : Matching (Remaining e.first e.second)) (z : Fin P.count → ℂ) (c : ℂ),
        c ≠ 0 ∧ (∀ j, z j ≠ 0) ∧ (∀ j, A (z j)) ∧
        contraction F e = product P z (fun j => star (z j)) c) :
    ∃ (m : ℕ) (ports : Fin m → ι) (z : Fin m → ℂ),
      m ≤ 2 ∧ (∀ j, z j ≠ 0) ∧ (∀ j, A (z j)) ∧
      ((∀ e, r.Disjoint e → XAt (attachFamily ports z F) e) ∨
        SecondCondition (attachFamily ports z F) r) := by
  classical
  have haway := fun e (her : e.Disjoint r) =>
    hcards e (nonzero_of_disjoint_X F e r her hr)
  choose P z c hc hz hAz he using haway
  by_cases hpaired : ∀ e (her : e.Disjoint r),
      mate (P e her) (e.residual r her).first = (e.residual r her).second
  · obtain ⟨w,hw,hAw,hx⟩ := normalize_paired_away_access hn A hAstar F r hr
      (fun e her => ⟨P e her,z e her,c e her,hc e her,hz e her,hAz e her,he e her,hpaired e her⟩)
    exact ⟨1,fun _ => r.first,fun _ => w,by omega,fun _ => hw,fun _ => hAw,Or.inl hx⟩
  · push Not at hpaired
    obtain ⟨s,hsr,hm⟩ := hpaired
    obtain ⟨w,v,hw,hv,hAw,hAv,hs⟩ := normalize_distinct_mates_access A hAstar F r s
      hsr.symm hr (P s hsr) (z s hsr) (c s hsr) (hc s hsr) (hz s hsr)
      (hAz s hsr) (he s hsr) hm
    refine ⟨2,![r.first,r.second],![w,v],by omega,?_,?_,Or.inr hs⟩
    · intro j; fin_cases j
      · exact hw
      · exact hv
    · intro j; fin_cases j
      · exact hAw
      · exact hAv

end Paper2.HighHeightNormalization
