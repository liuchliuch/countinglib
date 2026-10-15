import Counting.Algorithm.Holographic.Basic
import Counting.Model.FiniteSums

/-!
# Open covariance and closed invariance in S1

The proof follows the actual incidence-bijection argument of
`Holant.Holographic` and `ClosurePhysicalBridgeHolographicOpenAlgebra`, replacing
Boolean entries by an arbitrary finite domain. The input is S1's original
`KernelNetwork`; no alternate partition semantics or extra gadget resource is
introduced. Every ordered half-edge occurs exactly once in the port bijection.
-/

namespace Counting.Algorithm.Holographic

open scoped BigOperators
open Model

variable {D R B : Type} [Fintype D] [DecidableEq D] [CommSemiring R]

/-- Apply inverse columns at vertices and forward pullbacks at internal edges.
The complete incidence shape, including the boundary order, is retained. -/
def transform (G : KernelNetwork D R B) (M N : Kernel D R) : KernelNetwork D R B where
  shape := G.shape
  vertex := fun v => coordinateAction (fun _ => N) (G.vertex v)
  edge := fun e => pullback (G.edge e) M

omit [DecidableEq D] in
@[simp] theorem transform_shape (G : KernelNetwork D R B) (M N : Kernel D R) :
    (transform G M N).shape = G.shape := rfl

/-- The local vertex assignments are exactly the boundary and half-edge assignments. -/
def assignments (s : KernelNetworkShape B) :
    ((B → D) × ((Fin s.edges × Bool) → D)) ≃
      ((v : Fin s.vertices) → Fin (s.arity v) → D) :=
  (Equiv.sumArrowEquivProdArrow B (Fin s.edges × Bool) D).symm.trans
    ((Equiv.arrowCongr s.ports.symm (Equiv.refl D)).trans
      (Equiv.piCurry fun (v : Fin s.vertices) (_ : Fin (s.arity v)) => D))

omit [Fintype D] [DecidableEq D] in
@[simp] theorem assignments_apply (s : KernelNetworkShape B)
    (y : B → D) (w : (Fin s.edges × Bool) → D)
    (v : Fin s.vertices) (i : Fin (s.arity v)) :
    assignments s (y, w) v i = s.assignment y w v i := rfl

omit [DecidableEq D] in
/-- Expansion retains the ordered free ports as a separate boundary tensor. -/
theorem prod_vertex_action [Fintype B] [DecidableEq B] (s : KernelNetworkShape B)
    (f : (v : Fin s.vertices) → Model.Signature D R (s.arity v)) (N : Kernel D R)
    (x : B → D) (z : (Fin s.edges × Bool) → D) :
    (∏ v : Fin s.vertices,
      coordinateAction (fun _ => N) (f v) (s.assignment x z v)) =
    ∑ y : B → D, ∑ w : (Fin s.edges × Bool) → D,
      ((∏ i : B, N (x i) (y i)) *
        (∏ q : Fin s.edges × Bool, N (z q) (w q))) *
          ∏ v : Fin s.vertices, f v (s.assignment y w v) := by
  classical
  simp only [coordinateAction]
  rw [Fintype.prod_sum, ← (assignments s).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.prod_mul_distrib]
  congr 1
  change (∏ v : Fin s.vertices, ∏ i : Fin (s.arity v),
    N (s.assignment x z v i) (s.assignment y w v i)) = _
  rw [← Fintype.prod_sigma (fun p : Σ v : Fin s.vertices, Fin (s.arity v) =>
    N (s.assignment x z p.1 p.2) (s.assignment y w p.1 p.2))]
  rw [← s.ports.symm.prod_comp]
  change (∏ p : B ⊕ (Fin s.edges × Bool),
    N (Sum.elim x z (s.ports (s.ports.symm p)))
      (Sum.elim y w (s.ports (s.ports.symm p)))) = _
  simp only [Equiv.apply_symm_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]

omit [DecidableEq D] in
/-- Fubini for two distinct ordered ends per internal edge. -/
theorem sum_halfEdge_products (m : Nat) (f : Fin m → D → D → R) :
    (∑ z : (Fin m × Bool) → D,
      ∏ e : Fin m, f e (z (e, false)) (z (e, true))) =
    ∏ e : Fin m, ∑ a : D, ∑ b : D, f e a b := by
  classical
  rw [← (Equiv.curry (Fin m) Bool D).symm.sum_comp]
  change (∑ z : Fin m → Bool → D, ∏ e : Fin m, f e (z e false) (z e true)) = _
  rw [← Fintype.prod_sum (fun e (w : Bool → D) => f e (w false) (w true))]
  apply Finset.prod_congr rfl
  intro e _
  rw [← (Equiv.boolArrowEquivProd D).symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- Every internal edge cancels independently, with no simplicity assumptions. -/
theorem sum_edge_action (m : Nat) (E : Fin m → Kernel D R) (M N : Kernel D R)
    (hMN : M * N = 1) (y : (Fin m × Bool) → D) :
    (∑ z : (Fin m × Bool) → D,
      (∏ q : Fin m × Bool, N (z q) (y q)) *
        ∏ e : Fin m, pullback (E e) M (z (e, false)) (z (e, true))) =
    ∏ e : Fin m, E e (y (e, false)) (y (e, true)) := by
  simp only [Fintype.prod_prod_type, Fintype.prod_bool]
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_halfEdge_products m (fun e a b =>
    N b (y (e, true)) * N a (y (e, false)) * pullback (E e) M a b)]
  apply Finset.prod_congr rfl
  intro e _
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    edge_cancel (E e) M N hMN (y (e, false)) (y (e, true))

set_option backward.isDefEq.respectTransparency false in
/-- The actual open partition is covariant on its boundary, with ordinary
bilinear action at each boundary index. Empty domains and nullary vertices are allowed. -/
theorem raw_transform [Fintype B] [DecidableEq B]
    (G : KernelNetwork D R B) (M N : Kernel D R) (hMN : M * N = 1) :
    (transform G M N).raw = coordinateAction (fun _ => N) G.raw := by
  classical
  funext x
  simp only [KernelNetwork.raw, KernelNetwork.weight, transform]
  simp_rw [prod_vertex_action]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]
  calc
    _ = (∏ i : B, N (x i) (y i)) *
        ∑ w : (Fin G.shape.edges × Bool) → D,
          (∏ v : Fin G.shape.vertices, G.vertex v (G.shape.assignment y w v)) *
            ∑ z : (Fin G.shape.edges × Bool) → D,
              (∏ q : Fin G.shape.edges × Bool, N (z q) (w q)) *
                ∏ e : Fin G.shape.edges,
                  pullback (G.edge e) M (z (e, false)) (z (e, true)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ac_rfl
    _ = _ := by
      simp_rw [sum_edge_action G.shape.edges G.edge M N hMN]
      rfl

/-- Substantive S1 bridge: both sides are occurrence-list partitions, including
one occurrence per original vertex and one per supplied edge kernel. -/
theorem partition_transform [Fintype B] [DecidableEq B]
    (G : KernelNetwork D R B) (M N : Kernel D R) (hMN : M * N = 1) :
    (transform G M N).toOpenInstance.partition =
      coordinateAction (fun _ => N) G.toOpenInstance.partition := by
  have hp (H : KernelNetwork D R B) : H.toOpenInstance.partition = H.raw :=
    funext (KernelNetwork.partition_toOpenInstance H)
  rw [hp, hp]
  exact raw_transform G M N hMN

/-- There are no free port actions in the closed case. -/
theorem raw_transform_closed (G : KernelNetwork D R (Fin 0))
    (M N : Kernel D R) (hMN : M * N = 1) :
    (transform G M N).raw = G.raw := by
  rw [raw_transform G M N hMN, coordinateAction_nullary]

/-- Closed partition invariance stated entirely in S1's common occurrence model. -/
theorem partition_transform_closed (G : KernelNetwork D R (Fin 0))
    (M N : Kernel D R) (hMN : M * N = 1) :
    (transform G M N).toOpenInstance.partition = G.toOpenInstance.partition := by
  rw [partition_transform G M N hMN, coordinateAction_nullary]

/-- Applying the forward matrix to the resulting boundary recovers the old table.
This is a semantic identity, not a free boundary-gadget availability assertion. -/
theorem recover_boundary [Fintype B] [DecidableEq B]
    (G : KernelNetwork D R B) (M N : Kernel D R) (hMN : M * N = 1) :
    coordinateAction (fun _ => M) (transform G M N).toOpenInstance.partition =
      G.toOpenInstance.partition := by
  rw [partition_transform G M N hMN]
  exact coordinateAction_cancel (fun _ => M) (fun _ => N) (fun _ => hMN) _

end Counting.Algorithm.Holographic
