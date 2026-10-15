import Paper2.MatchingPropagation

/-! Two shared residual edges propagate by actual double-contraction support. -/
namespace Paper2.HighHeightReconstruction
open CommonPhase EndpointSelfLoop MatchingPropagation
variable {ι : Type}

/-- A named original edge in one actual residual matching. -/
def EdgeIn (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (r e : PortPair ι) (hre : r.Disjoint e) : Prop :=
  mate (P r) (r.residual e hre).first = (r.residual e hre).second

theorem literal_pairSum_forces_mate (P : Matching ι) (r e : PortPair ι)
    (her : e.Disjoint r) (hm : mate P e.first = e.second) :
    Forces (r.pairSum (literal P ℂ)) e.first e.second := by
  classical
  intro x hx
  obtain ⟨t,ht⟩ := pairSum_support _ r x hx
  have htx : Transversal P (r.fill x t) := by
    by_contra h
    simp [literal,h] at ht
  have hh := (transversal_iff_mate P _).mp htx e.first
  rw [hm,fill_other r x t e.second her.2.2.1 her.2.2.2,
    fill_other r x t e.first her.1 her.2.1] at hh
  exact hh

/-- A residual matching edge survives a second deletion on other ports. -/
theorem deck_pairSum_forces_edge (F : Tensor ℂ ι) (lam : PortPair ι → ℂ)
    (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (hd : MatchingDeck F lam P) (r t e : PortPair ι)
    (hrt : r.Disjoint t) (hre : r.Disjoint e) (het : e.Disjoint t)
    (he : EdgeIn P r e hre) :
    Forces ((r.residual t hrt).pairSum (contraction F r))
      (r.residual e hre).first (r.residual e hre).second := by
  rw [show contraction F r = fun x => lam r * literal (P r) ℂ x from hd r,
    PortPair.pairSum_mul]
  intro x hx
  apply literal_pairSum_forces_mate (P r) (r.residual t hrt) (r.residual e hre)
    (residual_disjoint r e t hre hrt het) he x
  intro hz
  exact hx (by simp [hz])

/-- Exact two-pair edge propagation (the X specialization of the source's
factor-comparison step). The input pairs need not be disjoint from each other. -/
theorem edge_in_of_two (F : Tensor ℂ ι) (lam : PortPair ι → ℂ)
    (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ r, lam r ≠ 0)
    (r s t e : PortPair ι) (hrs : ¬SamePair r s)
    (hrt : r.Disjoint t) (hst : s.Disjoint t)
    (hre : r.Disjoint e) (hse : s.Disjoint e) (hte : t.Disjoint e)
    (hr : EdgeIn P r e hre) (hs : EdgeIn P s e hse) : EdgeIn P t e hte := by
  by_contra ht
  have hr' := comparison_forces_same_matePair F r t e hrt hre hte (P t) (lam t)
    (hnz t) (hd t) ht (deck_pairSum_forces_edge F lam P hd r t e hrt hre hte.symm hr)
  have hs' := comparison_forces_same_matePair F s t e hst hse hte (P t) (lam t)
    (hnz t) (hd t) ht (deck_pairSum_forces_edge F lam P hd s t e hst hse hte.symm hs)
  exact hrs (hr'.trans hs'.symm)

end Paper2.HighHeightReconstruction
