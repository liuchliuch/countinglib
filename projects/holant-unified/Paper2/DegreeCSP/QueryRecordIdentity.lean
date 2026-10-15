import Paper2.DegreeCSP.QueryRoutes
import Paper2.DegreeCSP.EqualityDegreeRows
import Paper2.DegreeCSP.ComputationPaper2
import Holant.Proofs.Tetrahedral.EvenCSPReduction.Program

/-! The actual emitted ordered records equal the certified graph serialization.
This is list equality, including all repeated scopes and degree-zero rows. -/
namespace Paper2.DegreeCSP.QueryGraph
open Paper2.Tractable Paper2.ExactInput Paper2.Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {s : ℕ} {a : ℕ → ℕ} {k : ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (hk : 3 ≤ k) (r : Raw.Input s a k) (jK : Fin s) (hK : a jK.val = k)

def closedEndpoint {n : ℕ} (p : Fin n × Bool) : RawEndpoint := (p.1.val,p.2)

def storedRow (v : Fin (network G hk r).shape.vertices) : RawVertex :=
  (((labels G hk r jK hK).vertex v).val,List.ofFn (fun j =>
    closedEndpoint (ClosedLabelling.closedPortEquiv (network G hk r).shape ⟨v,j⟩)))

theorem original_endpoint (c : Fin r.val.factors.length) (j : Fin (r.val.factors.get c).2.length) :
    closedEndpoint (ClosedLabelling.closedPortEquiv (network G hk r).shape
      ⟨vertexIndex G hk r ⟨.inl c,(0 : Fin 1)⟩,
        Fin.cast (index_arity G hk r ⟨.inl c,(0 : Fin 1)⟩).symm j⟩) =
      ComputationLayout.originalEndpoint r ⟨c,j⟩ := by
  change closedEndpoint ((RawClosedNetwork.closedEndsEquiv _).symm
    ((network G hk r).shape.ports _)) = _
  rw [network_port,original_port]
  change ((edgeIndex G hk r (.inl ⟨c,j⟩)).val,false) = _
  rw [edgeIndex_outer_value]
  rfl

theorem variable_endpoint (i : Fin r.val.variables)
    (v : Fin (variableMacro hk r i).shape.vertices)
    (j : Fin ((variableMacro hk r i).shape.arity v)) :
    closedEndpoint (ClosedLabelling.closedPortEquiv (network G hk r).shape
      ⟨vertexIndex G hk r ⟨.inr i,v⟩,
        Fin.cast (index_arity G hk r ⟨.inr i,v⟩).symm j⟩) =
      EqualityTemplates.serializedEndpoint (ComputationLayout.outerOffset r i.val)
        (ComputationLayout.innerOffset r i.val) ((variableMacro hk r i).shape.ports ⟨v,j⟩) := by
  change closedEndpoint ((RawClosedNetwork.closedEndsEquiv _).symm
    ((network G hk r).shape.ports _)) = _
  rw [network_port,variable_port]
  generalize hq : (variableMacro hk r i).shape.ports ⟨v,j⟩ = q
  cases q with
  | inl b =>
    change ((edgeIndex G hk r (.inl ((Raw.grouping r).symm ⟨i,b⟩))).val,true) = _
    rw [edgeIndex_boundary_value]
    rfl
  | inr e =>
    change ((edgeIndex G hk r (.inr ⟨.inr i,e.1⟩)).val,e.2) = _
    rw [edgeIndex_inner_value]
    rfl

theorem original_row (c : Fin r.val.factors.length) :
    storedRow G hk r jK hK (vertexIndex G hk r ⟨.inl c,(0 : Fin 1)⟩) =
      ComputationLayout.originalRow r c := by
  apply Prod.ext
  · simp only [storedRow,labels,Equiv.symm_apply_apply,vertexLabel,Raw.label]
    rfl
  · change List.ofFn (fun j => closedEndpoint (ClosedLabelling.closedPortEquiv
      (network G hk r).shape ⟨vertexIndex G hk r ⟨.inl c,(0 : Fin 1)⟩,j⟩)) = _
    rw [List.ofFn_congr (index_arity G hk r ⟨.inl c,(0 : Fin 1)⟩)]
    apply congrArg List.ofFn
    funext j
    exact original_endpoint G hk r c j

theorem variable_rows (i : Fin r.val.variables) :
    List.ofFn (fun v : Fin (variableMacro hk r i).shape.vertices =>
      storedRow G hk r jK hK (vertexIndex G hk r ⟨.inr i,v⟩)) =
      ComputationLayout.variableRows jK.val r i := by
  calc
    _ = EqualityDegreeTemplates.networkRows (variableMacro hk r i) jK.val
        (ComputationLayout.outerOffset r i.val) (ComputationLayout.innerOffset r i.val) := by
      apply congrArg List.ofFn
      funext v
      apply Prod.ext
      · simp only [storedRow,labels,Equiv.symm_apply_apply,vertexLabel]
      · change List.ofFn (fun j => closedEndpoint (ClosedLabelling.closedPortEquiv
          (network G hk r).shape ⟨vertexIndex G hk r ⟨.inr i,v⟩,j⟩)) = _
        rw [List.ofFn_congr (index_arity G hk r ⟨.inr i,v⟩)]
        apply congrArg List.ofFn
        funext j
        exact variable_endpoint G hk r i v j
    _ = _ := by
      unfold variableMacro
      rw [← EqualityDegreeTemplates.degree_rows_eq_networkRows,
        EqualityDegreeTemplates.degree_rows]
      rfl

private theorem record_ext {r q : RawClosedNetwork}
    (vertices : r.vertices=q.vertices) (edges : r.edges=q.edges) : r=q := by
  cases r
  cases q
  cases vertices
  cases edges
  rfl

/-- The runtime output records have exactly the certified graph's row order,
local port order, edge orientation, and dictionary labels. -/
theorem raw_identity : raw G hk r jK hK = paper2RawRecord (ComputationLayout.raw jK.val r) := by
  apply record_ext
  · change List.ofFn (storedRow G hk r jK hK) = ComputationLayout.vertices jK.val r
    rw [Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Program.RecordsIdentity.sum_rows,
      Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Program.RecordsIdentity.sigma_rows
        (fun i : Fin r.val.variables => (variableMacro hk r i).shape.vertices)]
    change List.ofFn (fun c => storedRow G hk r jK hK (vertexIndex G hk r ⟨.inl c,(0 : Fin 1)⟩)) ++
      (List.finRange r.val.variables).flatMap (fun i => List.ofFn (fun v =>
        storedRow G hk r jK hK (vertexIndex G hk r ⟨.inr i,v⟩))) = _
    calc
      _ = List.ofFn (ComputationLayout.originalRow r) ++
          (List.finRange r.val.variables).flatMap (ComputationLayout.variableRows jK.val r) := by
        congr 1
        · apply congrArg List.ofFn
          funext c
          exact original_row G hk r jK hK c
        · apply congrArg ((List.finRange r.val.variables).flatMap)
          funext i
          exact variable_rows G hk r jK hK i
      _ = _ := by
        simp only [ComputationLayout.vertices,ComputationLayout.originalVertices,
          ComputationLayout.extraVertices,List.ofFn_eq_map]
  · change List.ofFn (fun _ : Fin (edgeCount hk r) => (0 : ℕ)) =
      List.replicate (ComputationLayout.edgeCount r) 0
    rw [edgeCount_layout]
    simp

include G hk hK in
theorem emitted_valid : (paper2RawRecord (ComputationLayout.raw jK.val r)).WellFormed s 1 a := by
  rw [← raw_identity G hk r jK hK]
  exact raw_valid G hk r jK hK

def query : {q : RawClosedNetwork // q.WellFormed s 1 a} :=
  ⟨paper2RawRecord (ComputationLayout.raw jK.val r),emitted_valid G hk r jK hK⟩

end
end Paper2.DegreeCSP.QueryGraph
