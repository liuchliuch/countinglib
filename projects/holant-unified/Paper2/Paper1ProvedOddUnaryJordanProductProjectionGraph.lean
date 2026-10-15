import Paper2.Paper1ProvedOddUnaryJordanProjectionGraph

/-! Arbitrary finite product-covector projections use the actual unary
rows adjoined by Jordan interpolation. The retained table carries its
executed controlled reduction to the original table. -/
namespace Paper2.Paper1Proved.OddUnary.JordanProjectionGraph
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {K : Type} [Field K] {r : ℕ} {a : ℕ→ℕ}
variable {H : (i : Fin r)→Holant.Signature K (a i.val)}

/-- A boundary permutation keeps all internal vertices, ordinary edges,
and exact original table labels. -/
def reorder {n : ℕ} (N : NoXOrdinaryGraphAdjoin.Output H n)
    (p : Equiv.Perm (Fin n)) : NoXOrdinaryGraphAdjoin.Output H n := by
  let M : Macro H n := ⟨N.network,N.labels,N.exact,N.ordinary⟩
  let R := M.reindex p
  exact ⟨R.network,R.labels,R.exact,R.edges⟩

theorem reorder_denote {n : ℕ} (N : NoXOrdinaryGraphAdjoin.Output H n)
    (p : Equiv.Perm (Fin n)) :
    (reorder N p).network.denote=Tensor.reindex p N.network.denote := by
  exact Macro.reindex_denote ⟨N.network,N.labels,N.exact,N.ordinary⟩ p

def covectors {m : ℕ} (z : Fin m→K) : Fin m→Bool→K :=
  fun i b=>if b then z i else 1

theorem covectors_nonzero {m : ℕ} (z : Fin m→K) (i : Fin m) : covectors z i≠0 := by
  intro zero
  have h := congrFun zero false
  exact one_ne_zero (by simpa only [covectors,Bool.false_eq_true,ite_false,Pi.zero_apply] using h)

variable [Algebra ℚ K] {degree m : ℕ}
variable {F : FixedField K degree} {u : Fin m→Bool→K}
variable (E : JordanUnaryAccess.FamilyExtension F H (List.ofFn u))

/-- Every selected cap is a literal row of the extended finite table. -/
def unaryRow (i : Fin m) : NoXOrdinaryGraphAdjoin.Output E.signatures 1 := by
  have member : u i∈List.ofFn u := List.mem_ofFn.mpr ⟨i,rfl⟩
  let j := Classical.choose (E.unary_literal (u i) member)
  let U := Macro.row j (fun x : Fin 1→Bool=>u i (x 0))
    (Classical.choose_spec (E.unary_literal (u i) member))
  exact ⟨U.network,U.labels,U.exact,U.edges⟩

theorem unaryRow_denote (i : Fin m) :
    (unaryRow E i).network.denote=fun x=>u i (x 0) := by
  exact Network.denote_corolla (fun x : Fin 1→Bool=>u i (x 0))

@[simp] theorem unaryRow_vertices (i : Fin m) :
    (unaryRow E i).network.shape.vertices=1 := rfl

@[simp] theorem unaryRow_edges (i : Fin m) :
    (unaryRow E i).network.shape.edges=0 := rfl

/-- The complete cap graph retains the requested last ordered pair. -/
def familyGraph (N : NoXOrdinaryGraphAdjoin.Output H (m+2)) :
    NoXOrdinaryGraphAdjoin.Output E.signatures 2 :=
  graph E.signatures m (RetainedTable.lift E.old E.old_literal N) (unaryRow E)

theorem familyGraph_denote (N : NoXOrdinaryGraphAdjoin.Output H (m+2)) :
    (familyGraph E N).network.denote=projection N.network.denote u := by
  rw [familyGraph,graph_denote]
  congr 1
  funext i b
  exact congrFun (unaryRow_denote E i) (fun _=>b)

theorem familyGraph_vertices (N : NoXOrdinaryGraphAdjoin.Output H (m+2)) :
    (familyGraph E N).network.shape.vertices=N.network.shape.vertices+m := by
  rw [familyGraph,graph_vertices]
  simp only [RetainedTable.lift_network,unaryRow_vertices,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]

theorem familyGraph_edges (N : NoXOrdinaryGraphAdjoin.Output H (m+2)) :
    (familyGraph E N).network.shape.edges=N.network.shape.edges+m := by
  rw [familyGraph,graph_edges]
  simp only [RetainedTable.lift_network,unaryRow_edges,Finset.sum_const_zero,add_zero]

/-- A prescribed permutation puts any desired ordered pair in the last
two slots before the exact product-covector contraction. -/
def orderedFamilyGraph (N : NoXOrdinaryGraphAdjoin.Output H (m+2))
    (p : Equiv.Perm (Fin (m+2))) : NoXOrdinaryGraphAdjoin.Output E.signatures 2 :=
  familyGraph E (reorder N p)

theorem orderedFamilyGraph_denote (N : NoXOrdinaryGraphAdjoin.Output H (m+2))
    (p : Equiv.Perm (Fin (m+2))) :
    (orderedFamilyGraph E N p).network.denote=
      projection (Tensor.reindex p N.network.denote) u := by
  rw [orderedFamilyGraph,familyGraph_denote,reorder_denote]

end
end Paper2.Paper1Proved.OddUnary.JordanProjectionGraph

namespace Paper2.Paper1Proved.OddUnary.IsotropicWSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
noncomputable section
variable {L : Paper2.ExactInput.Language} (S : IsotropicWSource L)

/-- All caps, the extended finite table and its controlled return program
are obtained internally from the proved W source. -/
theorem product_projection {m : ℕ}
    (N : NoXOrdinaryGraphAdjoin.Output S.source.H (m+2))
    (p : Equiv.Perm (Fin (m+2))) (u : Fin m→Bool→S.source.K)
    (nonzero : ∀i,u i≠0) :
    letI : Algebra ℚ S.source.K := S.source.K.algebra'
    ∃ E : JordanUnaryAccess.FamilyExtension S.source.F S.source.H (List.ofFn u),
      ∃ Q : NoXOrdinaryGraphAdjoin.Output E.signatures 2,
        Q.network.denote=JordanProjectionGraph.projection
          (Tensor.reindex p N.network.denote) u := by
  letI : Algebra ℚ S.source.K := S.source.K.algebra'
  obtain ⟨E⟩ := S.unary_family_extension (List.ofFn u) (by
    intro v member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    exact nonzero i)
  exact ⟨E,JordanProjectionGraph.orderedFamilyGraph E N p,
    JordanProjectionGraph.orderedFamilyGraph_denote E N p⟩

/-- The specialization caps `[1,z_i]` always have nonzero first entry.
Their exact binary matrix matches the polynomial projection endpoint. -/
theorem polynomial_matrix_projection {m : ℕ}
    (N : NoXOrdinaryGraphAdjoin.Output S.source.H (m+2))
    (p : Equiv.Perm (Fin (m+2))) (z : Fin m→S.source.K) :
    letI : Algebra ℚ S.source.K := S.source.K.algebra'
    ∃ E : JordanUnaryAccess.FamilyExtension S.source.F S.source.H
      (List.ofFn (JordanProjectionGraph.covectors z)),
      ∃ Q : NoXOrdinaryGraphAdjoin.Output E.signatures 2,
        ∀b c,Q.network.denote ![b,c]=
          ∑y:Fin m→Bool,(∏i,if y i then z i else 1)*
            (Tensor.reindex p N.network.denote) (Fin.append y ![b,c]) := by
  letI : Algebra ℚ S.source.K := S.source.K.algebra'
  obtain ⟨E,Q,hQ⟩ := S.product_projection N p (JordanProjectionGraph.covectors z)
    (JordanProjectionGraph.covectors_nonzero z)
  refine ⟨E,Q,?_⟩
  intro b c
  exact congrFun hQ ![b,c]

end
end Paper2.Paper1Proved.OddUnary.IsotropicWSource

