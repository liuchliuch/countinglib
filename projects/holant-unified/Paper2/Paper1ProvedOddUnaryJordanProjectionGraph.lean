import Paper2.Paper1ProvedOddUnaryJordanUnaryFamily
import Holant.Proofs.Hardness.GeneralOddNonisotropicFrame
import Mathlib.Data.Fintype.Prod

/-! Actual product-covector projections of arbitrary arity. All unary caps
are supplied by real retained row graphs, and every joining edge is ordinary
equality. The two uncontracted ports keep their prescribed order. -/
namespace Paper2.Paper1Proved.OddUnary.JordanProjectionGraph
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open GeneralOddNonisotropicFrame
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {K : Type} [Field K] {r : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin r)→Holant.Signature K (a i.val))

def head {n : ℕ} (N : NoXOrdinaryGraphAdjoin.Output H (n+1))
    (U : NoXOrdinaryGraphAdjoin.Output H 1) : NoXOrdinaryGraphAdjoin.Output H n := by
  let uses := capHead_uses (Set.range fun i:Fin r=>(⟨a i.val,H i⟩ : Holant.AnySignature K))
    U.network N.network (fun v=>⟨U.labels.vertex v,U.exact v⟩)
    (fun v=>⟨N.labels.vertex v,N.exact v⟩)
  exact {
    network := capHead U.network N.network
    labels := {
      vertex v := Classical.choose (uses v)
      vertex_arity v := congrArg Sigma.fst (Classical.choose_spec (uses v))
      edge _ := 0 }
    exact v := Classical.choose_spec (uses v)
    ordinary := capHead_ordinary U.network N.network U.ordinary N.ordinary }

theorem head_denote {n : ℕ} (N : NoXOrdinaryGraphAdjoin.Output H (n+1))
    (U : NoXOrdinaryGraphAdjoin.Output H 1) (x : Fin n→Bool) :
    (head H N U).network.denote x=
      ∑b:Bool,U.network.denote (fun _=>b)*N.network.denote (Fin.cons b x) := by
  simpa only [head,Fintype.sum_bool,add_comm] using capHead_denote U.network N.network x

/-- Last two arguments are retained; each preceding ordered argument is
capped by the corresponding covector. -/
def graph : (m : ℕ)→NoXOrdinaryGraphAdjoin.Output H (m+2)→
    (Fin m→NoXOrdinaryGraphAdjoin.Output H 1)→NoXOrdinaryGraphAdjoin.Output H 2
  | 0,N,_=>N
  | m+1,N,U=>graph m (head H N (U 0)) (fun i=>U i.succ)

def projection {m : ℕ} (f : Holant.Signature K (m+2)) (u : Fin m→Bool→K)
    (x : Fin 2→Bool) : K :=
  ∑y:Fin m→Bool,(∏i,u i (y i))*f (Fin.append y x)

theorem projection_zero (f : Holant.Signature K 2) (u : Fin 0→Bool→K) (x : Fin 2→Bool) :
    projection f u x=f x := by
  simp only [projection,Finset.univ_eq_empty,Finset.prod_empty,one_mul]
  rw [Fintype.sum_unique]
  congr 1
  funext i
  simp [Fin.append,Fin.addCases]

theorem projection_succ {m : ℕ} (f : Holant.Signature K (m+1+2))
    (u : Fin (m+1)→Bool→K) (x : Fin 2→Bool) :
    projection f u x=
      projection (fun z=>∑b:Bool,u 0 b*f (Fin.cons b z)) (fun i:Fin m=>u i.succ) x := by
  classical
  let E := Fin.consEquiv (fun _ : Fin (m+1)=>Bool)
  letI : Fintype (Bool × (Fin m→Bool)) :=
    instFintypeProd Bool (Fin m→Bool)
  unfold projection
  rw [←E.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [E,Fin.consEquiv_apply,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change (u 0 b*(∏i:Fin m,u i.succ (y i)))*f (Fin.append (Fin.cons b y) x)=_
  have he : Fin.append (Fin.cons b y) x=Fin.cons b (Fin.append y x) := by
    simpa using Fin.append_cons b y x
  rw [he]
  ring

theorem graph_denote (m : ℕ) (N : NoXOrdinaryGraphAdjoin.Output H (m+2))
    (U : Fin m→NoXOrdinaryGraphAdjoin.Output H 1) :
    (graph H m N U).network.denote=
      projection N.network.denote (fun i b=> (U i).network.denote (fun _=>b)) := by
  induction m with
  | zero=>
    funext x
    exact (projection_zero _ _ x).symm
  | succ m ih=>
    rw [graph,ih]
    funext x
    rw [projection_succ]
    congr 1
    funext z
    exact head_denote H N (U 0) z

theorem graph_vertices (m : ℕ) (N : NoXOrdinaryGraphAdjoin.Output H (m+2))
    (U : Fin m→NoXOrdinaryGraphAdjoin.Output H 1) :
    (graph H m N U).network.shape.vertices=N.network.shape.vertices+
      ∑i,(U i).network.shape.vertices := by
  induction m with
  | zero=>simp [graph]
  | succ m ih=>
    rw [graph,ih]
    change (capHead (U 0).network N.network).shape.vertices+
      (∑i:Fin m,(U i.succ).network.shape.vertices)=_
    rw [capHead_vertices,Fin.sum_univ_succ]
    omega

theorem graph_edges (m : ℕ) (N : NoXOrdinaryGraphAdjoin.Output H (m+2))
    (U : Fin m→NoXOrdinaryGraphAdjoin.Output H 1) :
    (graph H m N U).network.shape.edges=N.network.shape.edges+
      (∑i,(U i).network.shape.edges)+m := by
  induction m with
  | zero=>simp [graph]
  | succ m ih=>
    rw [graph,ih]
    change (capHead (U 0).network N.network).shape.edges+
      (∑i:Fin m,(U i.succ).network.shape.edges)+m=_
    rw [capHead_edges,Fin.sum_univ_succ]
    omega

end
end Paper2.Paper1Proved.OddUnary.JordanProjectionGraph
