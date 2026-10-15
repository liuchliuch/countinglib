import Paper2.HighHeightNormalization.TwoFactor
import Paper2.HighHeightNormalization.Seed

/-! Lemma 8.5, the case where the seed ports have distinct mates in one
nonzero away card. The splice coefficient is proved from the actual sums. -/
namespace Paper2.HighHeightNormalization
open MatchingPropagation CommonPhase EndpointSelfLoop
variable {ι : Type}

/-- The two concrete diagonal attachments preserve the native-X closing
kernel up to their displayed nonzero scalar. -/
theorem two_attachments_loop (F : Tensor ℂ ι) (r : PortPair ι) (z w : ℂ)
    (hratio : star z * w = z * star w) :
    contraction (attach r.first (binary z) (attach r.second (binary w) F)) r =
      fun x => (star z * w) * contraction F r x := by
  funext x
  change (∑ t : Bool, attach r.first (binary z) (attach r.second (binary w) F)
    (extendPair r.first r.second r.distinct x t)) = _
  simp only [attach_binary,extend_first,extend_second]
  have hw (t : Bool) : matingWeight z t * matingWeight w (!t) = star z * w := by
    cases t
    · rfl
    · exact hratio.symm
  simp_rw [← mul_assoc,hw]
  rw [← Finset.mul_sum]
  rfl

/-- Away from the attached ports, actual attachment commutes with the actual
pair contraction, including the residual subtype port map. -/
theorem contraction_attach_away (F : Tensor ℂ ι) (e : PortPair ι)
    (a : Remaining e.first e.second) (z : ℂ) :
    contraction (attach a.val (binary z) F) e = attach a (binary z) (contraction F e) := by
  funext x
  change (∑ t : Bool, attach a.val (binary z) F
    (extendPair e.first e.second e.distinct x t)) = _
  simp only [attach_binary,extend_other e x _ a.val a.property.1 a.property.2]
  rw [← Finset.mul_sum]
  rfl

/-- The two exceptional ARS factors and their mating parameters are extracted
from a genuine nonzero card. All other factors are forced literal by the
known seed card, and the ordered ratio is proved rather than assumed. -/
theorem distinct_mates_two_phase (F : Tensor ℂ ι) (r s : PortPair ι)
    (hrs : r.Disjoint s) (hr : XAt F r)
    (P : Matching (Remaining s.first s.second)) (z : Fin P.count → ℂ) (c : ℂ)
    (hc : c ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hs : contraction F s = product P z (fun i => star (z i)) c)
    (hm : mate P (s.residual r hrs.symm).first ≠ (s.residual r hrs.symm).second) :
    ∃ w v C : ℂ, w ≠ 0 ∧ v ≠ 0 ∧ C ≠ 0 ∧ star w * v = w * star v ∧
      contraction F s = fun x =>
        phaseWeight w (x (s.residual r hrs.symm).first) *
        phaseWeight v (x (s.residual r hrs.symm).second) * C * literal P ℂ x := by
  have hi : (P.ports.symm (s.residual r hrs.symm).first).1 ≠
      (P.ports.symm (s.residual r hrs.symm).second).1 := by
    intro he
    exact hm (mate_of_same_index P _ _ (s.residual r hrs.symm).distinct he)
  have hother : ∀ i, i ≠ (P.ports.symm (s.residual r hrs.symm).first).1 →
      i ≠ (P.ports.symm (s.residual r hrs.symm).second).1 → z i = star (z i) := by
    intro i hi hj
    exact factor_eq_of_disjoint_X F s r hrs.symm hr P z (fun i => star (z i)) c hz
      (fun i => by simpa using hz i) hs i ((avoids_iff_index P i _).mpr ⟨hi,hj⟩)
  obtain ⟨w,v,C,hw,hv,hC,hform⟩ := product_two_phase P z c hc hz _ _ hi hother
  have hflat := (double_comparison F s r hrs.symm hr).2
  rw [hs,hform] at hflat
  refine ⟨w,v,C,hw,hv,hC,two_phase_ratio P (s.residual r hrs.symm) hm w v C hw hv hC hflat,?_⟩
  exact hs.trans hform

/-- Two actual attachments supply precisely the two witnesses needed by
Lemma 8.4(2), retaining the original residual matching and its distinct mates. -/
theorem normalize_distinct_mates (F : Tensor ℂ ι) (r s : PortPair ι)
    (hrs : r.Disjoint s) (hr : XAt F r)
    (P : Matching (Remaining s.first s.second)) (z : Fin P.count → ℂ) (c : ℂ)
    (hc : c ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hs : contraction F s = product P z (fun i => star (z i)) c)
    (hm : mate P (s.residual r hrs.symm).first ≠ (s.residual r hrs.symm).second) :
    ∃ w v : ℂ, w ≠ 0 ∧ v ≠ 0 ∧
      SecondCondition (attach r.first (binary w) (attach r.second (binary v) F)) r := by
  obtain ⟨w,v,C,hw,hv,hC,hratio,hform⟩ :=
    distinct_mates_two_phase F r s hrs hr P z c hc hz hs hm
  refine ⟨w,v,hw,hv,?_,s,hrs,P,(w * star w) * (v * star v) * C,?_,?_,hm⟩
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

/-- The distinct-mates branch closes after the relative-EO terminal has
established the actual new weighted deck. It permits zero cards in that deck. -/
theorem distinct_mates_full_deck [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (r s : PortPair ι) (hrs : r.Disjoint s) (hr : XAt F r)
    (P : Matching (Remaining s.first s.second)) (z : Fin P.count → ℂ) (c : ℂ)
    (hc : c ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hs : contraction F s = product P z (fun i => star (z i)) c)
    (hm : mate P (s.residual r hrs.symm).first ≠ (s.residual r hrs.symm).second)
    (hstage : ∀ w v, w ≠ 0 → v ≠ 0 →
      ARSDeck (attach r.first (binary w) (attach r.second (binary v) F))) :
    ∃ w v : ℂ, w ≠ 0 ∧ v ≠ 0 ∧
      ∀ e, XAt (attach r.first (binary w) (attach r.second (binary v) F)) e := by
  obtain ⟨w,v,hw,hv,hcondition⟩ := normalize_distinct_mates F r s hrs hr P z c hc hz hs hm
  exact ⟨w,v,hw,hv,x_line_propagation hn _ (hstage w v hw hv) r (Or.inr hcondition)⟩

end Paper2.HighHeightNormalization
