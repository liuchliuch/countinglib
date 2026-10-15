import Paper2.HighHeightReconstruction.AwayInjectivity

/-! Exact projection onto a literal X factor on two named ports. -/
namespace Paper2.HighHeightReconstruction
open CommonPhase EndpointSelfLoop MatchingPropagation
variable {ι : Type}

/-- A concrete linear operator: contract the two ports, then restore their
literal X factor with its exact scalar one-half. -/
noncomputable def project (e : PortPair ι) (F : Tensor ℂ ι) : Tensor ℂ ι :=
  fun x => (Signature.disequality (x e.first) (x e.second) / 2) * e.pairSum F x

theorem fill_self (e : PortPair ι) (x : ι → Bool) (h : x e.second = !(x e.first)) :
    e.fill x (x e.first) = x := by
  rw [PortPair.fill_eq_extend]
  exact extendPair_restrict e.first e.second e.distinct x h

theorem disequality_ne_zero_iff (a b : Bool) :
    Signature.disequality (K := ℂ) a b ≠ 0 ↔ b = !a := by
  cases a <;> cases b <;> simp [Signature.disequality]

/-- The operator fixes a literal matching precisely on an already matched pair. -/
theorem project_literal_mate (P : Matching ι) (e : PortPair ι)
    (hm : mate P e.first = e.second) : project e (literal P ℂ) = literal P ℂ := by
  classical
  funext x
  by_cases hx : x e.second = !(x e.first)
  · have hfill (t : Bool) : literal P ℂ (e.fill x t) = literal P ℂ x := by
      have hh := fills_transversal_iff_of_mate P e hm x t (x e.first)
      rw [fill_self e x hx] at hh
      simp only [literal,hh]
    have hX : Signature.disequality (K := ℂ) (x e.first) (x e.second) = 1 := by
      cases ha : x e.first <;> simp [Signature.disequality,hx,ha]
    simp only [project,PortPair.pairSum,Fintype.sum_bool,hfill,hX]
    ring
  · have hX : Signature.disequality (K := ℂ) (x e.first) (x e.second) = 0 := by
      by_contra h
      exact hx ((disequality_ne_zero_iff _ _).mp h)
    have ht : ¬Transversal P x := by
      intro h
      exact hx (by simpa only [hm] using (transversal_iff_mate P x).mp h e.first)
    simp [project,hX,literal,ht]

theorem project_mul (e : PortPair ι) (c : ℂ) (F : Tensor ℂ ι) :
    project e (fun x => c * F x) = fun x => c * project e F x := by
  funext x
  unfold project
  rw [PortPair.pairSum_mul]
  ring

theorem project_lift (r e : PortPair ι) (hre : r.Disjoint e)
    (F : Tensor ℂ (Remaining r.first r.second)) (x : ι → Bool) :
    project e (fun y => F (restrict r.first r.second y)) x =
      project (r.residual e hre) F (restrict r.first r.second x) := by
  unfold project
  rw [PortPair.pairSum_lift]
  rfl

/-- Disjoint native-X sums commute with the full projection, including its
restored factor and its one-half scalar. -/
theorem pairSum_project (r e : PortPair ι) (hre : r.Disjoint e) (F : Tensor ℂ ι) :
    r.pairSum (project e F) = project e (r.pairSum F) := by
  funext x
  calc
    _ = (Signature.disequality (x e.first) (x e.second) / 2) * r.pairSum (e.pairSum F) x := by
      unfold PortPair.pairSum
      simp only [project,fill_other r x _ e.first hre.1.symm hre.2.2.1.symm,
        fill_other r x _ e.second hre.2.1.symm hre.2.2.2.symm,Finset.mul_sum]
      simp only [PortPair.pairSum,Finset.mul_sum]
    _ = _ := by rw [PortPair.pairSum_comm hre]; rfl

/-- The restored X pair has charge zero, so the projection preserves EO. -/
theorem project_chargeLayer [Fintype ι] (e : PortPair ι) (F : Tensor ℂ ι)
    (hF : Tensor.ChargeLayer F 0) : Tensor.ChargeLayer (project e F) 0 := by
  have hl : Tensor.ChargeLayer (contraction F e) 0 :=
    Tensor.contractX_chargeLayer (Tensor.reindex_chargeLayer (splitPorts e.first e.second e.distinct) hF)
  intro x hx
  have hX : Signature.disequality (K := ℂ) (x e.first) (x e.second) ≠ 0 := by
    intro hz
    apply hx
    simp [project,hz]
  have hop := (disequality_ne_zero_iff _ _).mp hX
  have hc : contraction F e (restrict e.first e.second x) ≠ 0 := by
    intro hz
    apply hx
    simp [project,PortPair.pairSum_eq_loop,hz,contraction] at *
  have hh := hl _ hc
  rwa [doubledCharge_restrict e.first e.second e.distinct x hop] at hh

/-- Local fixed-point identities on the actual subdeck recover the whole
EO tensor via the independently proved restricted-deck injectivity theorem. -/
theorem eq_project_of_away_fixed [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (e : PortPair ι) (F : Tensor ℂ ι) (hF : Tensor.ChargeLayer F 0)
    (hfix : ∀ r : PortPair ι, r.Disjoint e → project e (r.pairSum F) = r.pairSum F) :
    F = project e F := by
  apply eo_eq_of_away_contractions hn e F (project e F) hF (project_chargeLayer e F hF)
  intro r hre
  have hh : r.pairSum F = r.pairSum (project e F) := by
    rw [pairSum_project r e hre,hfix r hre]
  funext x
  have hp := congrFun hh (extendPair r.first r.second r.distinct x false)
  simpa only [PortPair.pairSum_eq_loop,PortPair.restrict_extend] using hp

/-- A shared edge of every appropriate actual residual matching lifts to a
literal factor of the full EO tensor. No abstract UPF or reconstruction oracle
is used: the displayed equality is the complete original coefficient table. -/
theorem persistent_edge_factor [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (hF : Tensor.ChargeLayer F 0)
    (lam : PortPair ι → ℂ)
    (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (hd : MatchingDeck F lam P) (e : PortPair ι)
    (hp : ∀ (r : PortPair ι) (hre : r.Disjoint e),
      mate (P r) (r.residual e hre).first = (r.residual e hre).second) :
    F = project e F := by
  apply eq_project_of_away_fixed hn e F hF
  intro r hre
  rw [PortPair.pairSum_deck hd r]
  funext x
  rw [project_mul]
  change lam r * project e (fun y => literal (P r) ℂ (restrict r.first r.second y)) x = _
  rw [project_lift r e hre,project_literal_mate (P r) (r.residual e hre) (hp r hre)]

end Paper2.HighHeightReconstruction
