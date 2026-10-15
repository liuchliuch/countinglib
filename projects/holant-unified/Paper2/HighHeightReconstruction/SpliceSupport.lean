import Paper2.HighHeightReconstruction.EdgeTransfer

/-! Exact support characterization of actual native-X deletion of a literal
matching. This exposes the splice rule without any enumeration assumption. -/
namespace Paper2.HighHeightReconstruction
open CommonPhase EndpointSelfLoop MatchingPropagation
variable {ι : Type}

theorem literal_pairSum_forces_splice (P : Matching ι) (e : PortPair ι) (a b : ι)
    (ha : mate P a = e.first) (hb : mate P b = e.second)
    (ha₁ : a ≠ e.first) (ha₂ : a ≠ e.second)
    (hb₁ : b ≠ e.first) (hb₂ : b ≠ e.second) :
    Forces (e.pairSum (literal P ℂ)) a b := by
  have h := pairSum_product_forces_splice P (fun _ => (1 : ℂ)) (fun _ => 1) 1
    one_ne_zero (fun _ => one_ne_zero) (fun _ => one_ne_zero) e a b ha hb ha₁ ha₂ hb₁ hb₂
  simpa [product_eq_literal] using h

/-- A pair of surviving ports is forced opposite by the actual two-summand
contraction exactly when its original matching edge survives, or the two
edges are spliced through the deleted ports. -/
theorem literal_pairSum_forces_iff (P : Matching ι) (e : PortPair ι) (a b : ι)
    (hab : a ≠ b) (ha₁ : a ≠ e.first) (ha₂ : a ≠ e.second)
    (hb₁ : b ≠ e.first) (hb₂ : b ≠ e.second) :
    Forces (e.pairSum (literal P ℂ)) a b ↔
      mate P a = b ∨
      (mate P a = e.first ∧ mate P b = e.second) ∨
      (mate P a = e.second ∧ mate P b = e.first) := by
  constructor
  · intro h
    by_cases hm : mate P a = b
    · exact Or.inl hm
    · exact Or.inr (literal_forces_deleted_mates P e a b hab hm ha₁ ha₂ hb₁ hb₂ h)
  · rintro (hm | ⟨ha,hb⟩ | ⟨ha,hb⟩)
    · exact literal_pairSum_forces_mate P e ⟨a,b,hab⟩ ⟨ha₁,ha₂,hb₁,hb₂⟩ hm
    · exact literal_pairSum_forces_splice P e a b ha hb ha₁ ha₂ hb₁ hb₂
    · exact (literal_pairSum_forces_splice P e b a hb ha hb₁ hb₂ ha₁ ha₂).symm

/-- Double-deletion support, with the nonzero scalars cancelled, agrees in
both orders on every surviving pair. This is the finite-atlas compatibility
bridge at the actual tensor level. -/
theorem double_literal_forces_iff (F : Tensor ℂ ι) (lam : PortPair ι → ℂ)
    (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ r, lam r ≠ 0)
    (e s r : PortPair ι) (hes : e.Disjoint s) (her : e.Disjoint r) (hsr : s.Disjoint r) :
    Forces ((e.residual s hes).pairSum (literal (P e) ℂ))
      (e.residual r her).first (e.residual r her).second ↔
    Forces ((s.residual e hes.symm).pairSum (literal (P s) ℂ))
      (s.residual r hsr).first (s.residual r hsr).second := by
  have transfer (e s r : PortPair ι) (hes : e.Disjoint s) (her : e.Disjoint r)
      (hsr : s.Disjoint r)
      (h : Forces ((e.residual s hes).pairSum (literal (P e) ℂ))
        (e.residual r her).first (e.residual r her).second) :
      Forces ((s.residual e hes.symm).pairSum (literal (P s) ℂ))
        (s.residual r hsr).first (s.residual r hsr).second := by
    have he : Forces ((e.residual s hes).pairSum (contraction F e))
        (e.residual r her).first (e.residual r her).second := by
      rw [show contraction F e = _ from hd e,PortPair.pairSum_mul]
      exact (Forces.mul_iff _ (hnz e) _ _ _).mpr h
    have hs := double_forces_transfer F e s r hes her hsr he
    rw [show contraction F s = _ from hd s,PortPair.pairSum_mul] at hs
    exact (Forces.mul_iff _ (hnz s) _ _ _).mp hs
  exact ⟨transfer e s r hes her hsr, transfer s e r hes.symm hsr her⟩

end Paper2.HighHeightReconstruction
