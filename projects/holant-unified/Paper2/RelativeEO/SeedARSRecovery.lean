import Paper2.HighHeightReconstruction.AwayInjectivity
import Paper2.RelativeEO.MatingARS

/-! Recovering ARS from one actual literal seed card.  Only the cards avoiding
the seed ports are used.  Their nonzero real double contractions align their
ARS phases, and the exact zero-loop triangle recovers the original EO table.
This argument applies at arity six as well as at higher arity. -/
namespace Paper2.RelativeEO
open Tractable CommonPhase EndpointSelfLoop MatchingPropagation
open scoped BigOperators
variable {ι : Type}

/-- A scalar version of conjugate-complement symmetry, retaining the phase. -/
def HasARSPhase (c : ℂ) (F : Tensor ℂ ι) : Prop :=
  ∀ x, star (F (fun i => !(x i))) * c = F x * star c

theorem isARS_has_phase {F : Tensor ℂ ι} (h : IsARS F) :
    ∃ c : ℂ, c ≠ 0 ∧ HasARSPhase c F := by
  obtain ⟨P,a,c,hc,_,rfl⟩ := h
  refine ⟨c,hc,fun x => ?_⟩
  have hp : star (∏ j, WeightedMatching.binary (a j) (star (a j))
      (!(x (P.ports (j,false)))) (!(x (P.ports (j,true))))) =
      ∏ j, WeightedMatching.binary (a j) (star (a j))
        (x (P.ports (j,false))) (x (P.ports (j,true))) := by
    rw [star_prod]
    apply Finset.prod_congr rfl
    intro j _
    cases x (P.ports (j,false)) <;> cases x (P.ports (j,true)) <;>
      simp [WeightedMatching.binary]
  simp only [product,star_mul,hp]
  ring

theorem hasARSPhase_loop {c : ℂ} {F : Tensor ℂ ι}
    (h : HasARSPhase c F) (a b : ι) (hab : a ≠ b) :
    HasARSPhase c (loop a b hab F) := by
  intro x
  have hh := congrArg (fun z : ℂ => star z * c)
    (loop_complement a b hab F x).symm
  rw [hh]
  change star (∑ t : Bool, F (fun i => !(extendPair a b hab x t i))) * c =
    (∑ t : Bool, F (extendPair a b hab x t)) * star c
  simp only [star_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  exact h (extendPair a b hab x t)

theorem hasARSPhase_pairSum {c : ℂ} {F : Tensor ℂ ι}
    (h : HasARSPhase c F) (e : PortPair ι) : HasARSPhase c (e.pairSum F) := by
  intro x
  rw [PortPair.pairSum_eq_loop,PortPair.pairSum_eq_loop]
  exact hasARSPhase_loop h e.first e.second e.distinct (restrict e.first e.second x)

theorem hasARSPhase_change {c d : ℂ} (hc : c ≠ 0)
    (hcd : star d * c = d * star c) {F : Tensor ℂ ι}
    (h : HasARSPhase c F) : HasARSPhase d F := by
  intro x
  apply mul_right_cancel₀ hc
  calc
    (star (F (fun i => !(x i))) * d) * c =
        (star (F (fun i => !(x i))) * c) * d := by ring
    _ = (F x * star c) * d := by rw [h]
    _ = F x * (star d * c) := by rw [hcd]; ring
    _ = (F x * star d) * c := by ring

theorem pairSum_star (e : PortPair ι) (F : Tensor ℂ ι) (x : ι → Bool) :
    star (e.pairSum F x) = e.pairSum (fun y => star (F y)) x := by
  simp only [PortPair.pairSum,star_sum]

theorem pairSum_complement (e : PortPair ι) (F : Tensor ℂ ι) (x : ι → Bool) :
    e.pairSum F (fun i => !(x i)) = e.pairSum (fun y => F (fun i => !(y i))) x := by
  rw [PortPair.pairSum_eq_loop,PortPair.pairSum_eq_loop,loop_complement]
  rfl

private theorem phase_scalar_of_real_table {c d : ℂ} (J : Tensor ℂ ι)
    (hJstar : ∀ x, star (J x) = J x)
    (hJcomp : ∀ x, J (fun i => !(x i)) = J x)
    (hJne : ∃ x, J x ≠ 0) (hphase : HasARSPhase c (fun x => d * J x)) :
    star d * c = d * star c := by
  obtain ⟨x,hx⟩ := hJne
  have hh := hphase x
  change star (d * J (fun i => !(x i))) * c = (d * J x) * star c at hh
  rw [hJcomp,star_mul,hJstar] at hh
  apply mul_right_cancel₀ hx
  linear_combination hh

/-- Every actual card away from a literal seed has the seed's ARS phase.
The phase comparison uses its nonzero double contraction, rather than a
postulated relation between displayed matching scalars. -/
theorem away_card_has_seed_phase (F : Tensor ℂ ι) (r e : PortPair ι)
    (her : e.Disjoint r) (P : XMatching (Remaining r.first r.second))
    (d : ℂ) (hd : d ≠ 0)
    (hseed : contraction F r = fun x => d * literal P ℂ x)
    (hdeck : ARSDeck F) : HasARSPhase d (contraction F e) := by
  classical
  have hX : XAt F r := ⟨P,d,hd,hseed⟩
  obtain ⟨c,hc,hphase⟩ := isARS_has_phase
    (hdeck e (nonzero_of_disjoint_X F e r her hX))
  have hphaseLift : HasARSPhase c (e.pairSum F) := by
    intro x
    rw [PortPair.pairSum_eq_loop,PortPair.pairSum_eq_loop]
    exact hphase (restrict e.first e.second x)
  let I : Tensor ℂ ι := fun x => literal P ℂ (restrict r.first r.second x)
  let J : Tensor ℂ ι := e.pairSum I
  have hIstar : ∀ x, star (I x) = I x := by
    intro x
    rcases literal_eq_zero_or_one (K := ℂ) P (restrict r.first r.second x) with h | h <;>
      simp [I,h]
  have hIcomp : ∀ x, I (fun i => !(x i)) = I x := by
    intro x
    exact literal_complement P (restrict r.first r.second x)
  have hJstar : ∀ x, star (J x) = J x := by
    intro x
    change star (e.pairSum I x) = e.pairSum I x
    rw [pairSum_star]
    exact congrFun (congrArg e.pairSum (funext hIstar)) x
  have hJcomp : ∀ x, J (fun i => !(x i)) = J x := by
    intro x
    change e.pairSum I (fun i => !(x i)) = e.pairSum I x
    rw [pairSum_complement]
    exact congrFun (congrArg e.pairSum (funext hIcomp)) x
  have hsum : r.pairSum (e.pairSum F) = fun x => d * J x := by
    rw [← PortPair.pairSum_comm her F]
    have hseedLift : r.pairSum F = fun x => d * I x := by
      funext x
      rw [PortPair.pairSum_eq_loop]
      exact congrFun hseed (restrict r.first r.second x)
    rw [hseedLift,PortPair.pairSum_mul]
  have hJne : ∃ x, J x ≠ 0 := by
    obtain ⟨y,hy⟩ := pairSum_isX_nonzero (r.residual e her.symm) hX
    let x := extendPair r.first r.second r.distinct y false
    refine ⟨x,?_⟩
    have hval : r.pairSum (e.pairSum F) x =
        (r.residual e her.symm).pairSum (contraction F r) y := by
      rw [← PortPair.pairSum_comm her F]
      have hlift : r.pairSum F = fun z => contraction F r (restrict r.first r.second z) := by
        funext z
        exact PortPair.pairSum_eq_loop r F z
      rw [hlift,PortPair.pairSum_lift r e her.symm,PortPair.restrict_extend]
    intro hzero
    have hzero' : r.pairSum (e.pairSum F) x = 0 := by
      rw [hsum]
      change d * J x = 0
      rw [hzero,mul_zero]
    exact hy (hval.symm.trans hzero')
  have hcd : star d * c = d * star c :=
    phase_scalar_of_real_table J hJstar hJcomp hJne
      (hsum ▸ hasARSPhase_pairSum hphaseLift r)
  exact hasARSPhase_change hc hcd hphase

/-- The exact zero-loop injectivity argument needs only one occupied and one
unoccupied port away from the fixed pair; the third port supplies either the
ordinary triangle or its complemented version. -/
theorem eo_zero_of_away_contractions_six [Fintype ι] (hn : 6 ≤ Fintype.card ι)
    (e : PortPair ι) (F : Tensor ℂ ι) (heo : Tensor.ChargeLayer F 0)
    (hz : ∀ r : PortPair ι, r.Disjoint e → contraction F r = 0) : F = 0 := by
  classical
  funext x
  change F x = 0
  by_contra hx
  have hc := heo x hx
  have hw : 3 ≤ weight x := by unfold doubledCharge at hc; omega
  have hw' : 3 ≤ weight (fun i => !(x i)) := by
    have := weight_complement_add x
    unfold doubledCharge at hc
    omega
  let T : Finset ι := Finset.univ.filter (fun i => x i = true)
  let Z : Finset ι := Finset.univ.filter (fun i => x i = false)
  have hT : T.card = weight x := by simp only [T,Finset.card_filter,weight]
  have hZ : Z.card = weight (fun i => !(x i)) := by
    simp only [Z,Finset.card_filter,weight]
    apply Finset.sum_congr rfl
    intro i _
    simp
  have hTc : 0 < (T \ pairPorts e).card := by
    have h₁ := Finset.card_sdiff_add_card_inter T (pairPorts e)
    have h₂ := Finset.card_le_card (Finset.inter_subset_right (s₁ := T) (s₂ := pairPorts e))
    simp only [card_pairPorts] at h₂
    omega
  have hZc : 0 < (Z \ pairPorts e).card := by
    have h₁ := Finset.card_sdiff_add_card_inter Z (pairPorts e)
    have h₂ := Finset.card_le_card (Finset.inter_subset_right (s₁ := Z) (s₂ := pairPorts e))
    simp only [card_pairPorts] at h₂
    omega
  obtain ⟨a,ha⟩ := Finset.card_pos.mp hTc
  obtain ⟨c,hc'⟩ := Finset.card_pos.mp hZc
  have ha' : a ≠ e.first ∧ a ≠ e.second := by simpa using (Finset.mem_sdiff.mp ha).2
  have hc'' : c ≠ e.first ∧ c ≠ e.second := by simpa using (Finset.mem_sdiff.mp hc').2
  have hat : x a = true := (Finset.mem_filter.mp (Finset.mem_sdiff.mp ha).1).2
  have hcf : x c = false := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hc').1).2
  let A : Remaining e.first e.second := ⟨a,ha'⟩
  let C : Remaining e.first e.second := ⟨c,hc''⟩
  have hrem := remaining_card e.first e.second e.distinct
  obtain ⟨b,hba,hbc⟩ := exists_third (by omega : 3 ≤ Fintype.card (Remaining e.first e.second)) A C
  have hab : a ≠ b.val := fun h => hba (Subtype.ext h.symm)
  have hac : a ≠ c := by intro h; rw [h,hcf] at hat; contradiction
  have hbc' : b.val ≠ c := fun h => hbc (Subtype.ext h)
  have hzab := hz ⟨a,b.val,hab⟩ ⟨ha'.1,ha'.2,b.property.1,b.property.2⟩
  have hzac := hz ⟨a,c,hac⟩ ⟨ha'.1,ha'.2,hc''.1,hc''.2⟩
  have hzbc := hz ⟨b.val,c,hbc'⟩ ⟨b.property.1,b.property.2,hc''.1,hc''.2⟩
  cases hb : x b.val with
  | true =>
    exact hx (Paper2.HighHeightReconstruction.coefficient_zero_of_selected_three
      F x a b.val c hab hac hbc' hat hb hcf hzab hzac hzbc)
  | false =>
    let G : Tensor ℂ ι := fun y => F (fun i => !(y i))
    have hGz (r : PortPair ι) (hr : r.Disjoint e) : contraction G r = 0 := by
      funext y
      change loop r.first r.second r.distinct (fun z => F (fun i => !(z i))) y = 0
      rw [loop_complement]
      exact congrFun (hz r hr) (fun i => !(y i))
    have hh := Paper2.HighHeightReconstruction.coefficient_zero_of_selected_three
      G (fun i => !(x i)) c b.val a hbc'.symm hac.symm hab.symm
      (by simp [hcf]) (by simp [hb]) (by simp [hat])
      (hGz ⟨c,b.val,hbc'.symm⟩ ⟨hc''.1,hc''.2,b.property.1,b.property.2⟩)
      (hGz ⟨c,a,hac.symm⟩ ⟨hc''.1,hc''.2,ha'.1,ha'.2⟩)
      (hGz ⟨b.val,a,hab.symm⟩ ⟨b.property.1,b.property.2,ha'.1,ha'.2⟩)
    exact hx (by simpa [G] using hh)

/-- A single normalized genuine card suffices to recover conjugate-complement
symmetry of the entire EO table, including the previously exceptional arity
six.  All away cards are the actual native-X contractions of this table. -/
theorem hasARSPhase_of_seed [Fintype ι] (hn : 6 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (heo : Tensor.ChargeLayer F 0) (r : PortPair ι)
    (P : XMatching (Remaining r.first r.second)) (d : ℂ) (hd : d ≠ 0)
    (hseed : contraction F r = fun x => d * literal P ℂ x)
    (hdeck : ARSDeck F) : HasARSPhase d F := by
  let H : Tensor ℂ ι := fun x => star (F (fun i => !(x i))) * d - F x * star d
  have hH : Tensor.ChargeLayer H 0 := by
    intro x hx
    by_cases hfx : F x = 0
    · have hcomp : F (fun i => !(x i)) ≠ 0 := by
        intro hzero
        exact hx (by simp [H,hfx,hzero])
      have hh := heo (fun i => !(x i)) hcomp
      rw [doubledCharge_complement] at hh
      exact neg_eq_zero.mp hh
    · exact heo x hfx
  have hzero : H = 0 := by
    apply eo_zero_of_away_contractions_six hn r H hH
    intro e her
    have hp := away_card_has_seed_phase F r e her P d hd hseed hdeck
    funext y
    change (∑ t : Bool, (star (F (fun i => !(extendPair e.first e.second e.distinct y t i))) * d -
      F (extendPair e.first e.second e.distinct y t) * star d)) = 0
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.sum_mul,← star_sum]
    change star (loop e.first e.second e.distinct (fun x => F (fun i => !(x i))) y) * d -
      loop e.first e.second e.distinct F y * star d = 0
    rw [loop_complement]
    exact sub_eq_zero.mpr (hp y)
  intro x
  exact sub_eq_zero.mp (congrFun hzero x)

theorem hasARSPhase_normalized {c : ℂ} (hc : c ≠ 0) {F : Tensor ℂ ι}
    (h : HasARSPhase c F) :
    ∀ x, star (F (fun i => !(x i)) / c) = F x / c := by
  intro x
  rw [star_div₀]
  apply (div_eq_div_iff (by simpa using hc) hc).mpr
  exact h x

/-- The seed's phase is an actual algebraic contraction coefficient.  Hence
recovery produces the source's exact algebraic ProjectiveARS predicate. -/
theorem projectiveARS_of_seed_deck {n : ℕ} (hn : 6 ≤ n)
    (f : Signature AlgebraicComplex n) (heo : Tensor.ChargeLayer f 0)
    (r : PortPair (Fin n)) (hseed : XAt (fun x => (f x : ℂ)) r)
    (hdeck : ARSDeck (fun x => (f x : ℂ))) : ProjectiveARS f := by
  obtain ⟨P,d,hd,hseed⟩ := hseed
  let φ : AlgebraicComplex →+* ℂ := (algebraicClosure ℚ ℂ).val.toRingHom
  let y := word P (fun _ => false)
  let c : AlgebraicComplex := loop r.first r.second r.distinct f y
  have hc : (c : ℂ) = d := by
    have hm := loop_map φ.toAddMonoidHom r.first r.second r.distinct f y
    have hv := congrFun hseed y
    rw [literal_word,mul_one] at hv
    exact hm.symm.trans hv
  have hcne : c ≠ 0 := by
    intro hzero
    apply hd
    rw [← hc,hzero]
    rfl
  have heoC : Tensor.ChargeLayer (fun x => (f x : ℂ)) 0 := by
    intro x hx
    exact heo x (fun hzero => hx (by change (f x : ℂ) = 0; rw [hzero]; rfl))
  have hp := hasARSPhase_normalized hd
    (hasARSPhase_of_seed (by simpa using hn) (fun x => (f x : ℂ)) heoC r P d hd hseed hdeck)
  refine ⟨c,hcne,fun x => ?_⟩
  have hh := hp x
  rw [← hc] at hh
  simpa only [div_eq_mul_inv,mul_comm] using hh.symm

end Paper2.RelativeEO
