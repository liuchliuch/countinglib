import Paper2.Charge
import Paper2.Tractable.Criteria

/-! A common support side forces every nonzero closed-network summand onto the
central layer at every vertex.  Thus replacing labels by their central tables
preserves the exact original graph's value, rather than deleting any vertex. -/
namespace Paper2.Network
open scoped BigOperators

variable {K : Type*} [CommSemiring K]

def centralize (N : Network K 0) : Network K 0 where
  shape := N.shape
  vertex v := Signature.centralRestriction (N.vertex v)
  edge := N.edge

theorem central_of_one_sided_term (N : Network K 0)
    (hX : ∀ e, N.edge e = Signature.disequality)
    (hside : (∀ v x, N.vertex v x ≠ 0 → 0 ≤ doubledCharge x) ∨
      (∀ v x, N.vertex v x ≠ 0 → doubledCharge x ≤ 0))
    (z : (Fin N.shape.edges × Bool) → Bool)
    (hz : N.assignmentTerm Fin.elim0 z ≠ 0) (v : Fin N.shape.vertices) :
    2 * weight (N.shape.assignment Fin.elim0 z v) = N.shape.arity v := by
  have hsum := N.sum_doubledCharge_eq_external_of_term hX Fin.elim0 z hz
  have hzero : (∑ w, doubledCharge (N.shape.assignment Fin.elim0 z w)) = 0 := by
    simpa [doubledCharge, weight] using hsum
  have hv : doubledCharge (N.shape.assignment Fin.elim0 z v) = 0 := by
    rcases hside with hside | hside
    · exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun w _ => hside w _ (N.vertex_ne_zero_of_term _ _ hz w))).mp hzero v (Finset.mem_univ v)
    · have hneg : (∑ w, -doubledCharge (N.shape.assignment Fin.elim0 z w)) = 0 := by
        rw [Finset.sum_neg_distrib, hzero, neg_zero]
      have hv := (Finset.sum_eq_zero_iff_of_nonneg
        (fun w _ => neg_nonneg.mpr (hside w _ (N.vertex_ne_zero_of_term _ _ hz w)))).mp
        hneg v (Finset.mem_univ v)
      exact neg_eq_zero.mp hv
  simp only [doubledCharge, Fintype.card_fin] at hv
  omega

theorem centralize_assignmentTerm (N : Network K 0)
    (hX : ∀ e, N.edge e = Signature.disequality)
    (hside : (∀ v x, N.vertex v x ≠ 0 → 0 ≤ doubledCharge x) ∨
      (∀ v x, N.vertex v x ≠ 0 → doubledCharge x ≤ 0))
    (z : (Fin N.shape.edges × Bool) → Bool) :
    N.centralize.assignmentTerm Fin.elim0 z = N.assignmentTerm Fin.elim0 z := by
  classical
  by_cases hc : ∀ v, 2 * weight (N.shape.assignment Fin.elim0 z v) = N.shape.arity v
  · simp only [assignmentTerm, centralize, Signature.centralRestriction, hc, ↓reduceIte]
    rfl
  · obtain ⟨v, hv⟩ := not_forall.mp hc
    have hz : N.assignmentTerm Fin.elim0 z = 0 := by
      by_contra hz
      exact hv (N.central_of_one_sided_term hX hside z hz v)
    rw [hz]
    apply mul_eq_zero_of_left
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    exact if_neg hv

theorem centralize_denote (N : Network K 0)
    (hX : ∀ e, N.edge e = Signature.disequality)
    (hside : (∀ v x, N.vertex v x ≠ 0 → 0 ≤ doubledCharge x) ∨
      (∀ v x, N.vertex v x ≠ 0 → doubledCharge x ≤ 0)) :
    N.centralize.denote Fin.elim0 = N.denote Fin.elim0 := by
  change (∑ z, N.centralize.assignmentTerm Fin.elim0 z) = ∑ z, N.assignmentTerm Fin.elim0 z
  exact Finset.sum_congr rfl (fun z _ => N.centralize_assignmentTerm hX hside z)

end Paper2.Network
