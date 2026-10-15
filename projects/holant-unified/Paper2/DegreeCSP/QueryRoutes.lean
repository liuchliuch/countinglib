import Paper2.DegreeCSP.QueryIndices

/-! Every stored endpoint is the same endpoint of the actual compiler graph.
These equations retain the original local ordinal, including repeated scopes. -/
namespace Paper2.DegreeCSP.QueryGraph
open Paper2.Tractable Paper2.ExactInput Paper2.Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {s : ℕ} {a : ℕ → ℕ} {k : ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (hk : 3 ≤ k) (r : Raw.Input s a k)

theorem index_arity (p : SubVertex G hk r) :
    (network G hk r).shape.arity (vertexIndex G hk r p) = (finiteGraph G hk r).arity p := by
  simp only [network,OrderedEnumeration.graph,Equiv.symm_apply_apply]

private theorem transported_fin_val {A : Type} (f : A → ℕ) {x y : A}
    (h : x=y) (j : Fin (f x)) : (h ▸ j : Fin (f y)).val=j.val := by
  cases h
  rfl

theorem index_port (p : SubVertex G hk r) (j : Fin ((finiteGraph G hk r).arity p)) :
    ((vertexIndex G hk r).symm.sigmaCongrLeft
      (β := fun p : SubVertex G hk r => Fin ((finiteGraph G hk r).arity p))).symm ⟨p,j⟩ =
      ⟨vertexIndex G hk r p,Fin.cast (index_arity G hk r p).symm j⟩ := by
  dsimp only [Equiv.sigmaCongrLeft,Equiv.coe_fn_symm_mk]
  apply Sigma.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    apply Fin.ext
    simpa only [Fin.val_cast] using transported_fin_val (finiteGraph G hk r).arity
      ((vertexIndex G hk r).symm_apply_apply p).symm j

theorem network_port (p : SubVertex G hk r) (j : Fin ((finiteGraph G hk r).arity p)) :
    (network G hk r).shape.ports
      ⟨vertexIndex G hk r p,Fin.cast (index_arity G hk r p).symm j⟩ =
      Sum.map id (fun e => (edgeIndex G hk r e.1,e.2)) ((finiteGraph G hk r).ports ⟨p,j⟩) := by
  rw [← index_port]
  simp only [network,OrderedEnumeration.graph,Equiv.trans_apply,Equiv.apply_symm_apply,
    Equiv.sumCongr_apply,Equiv.prodCongr_apply]
  rfl

theorem original_port (c : Fin r.val.factors.length) (j : Fin (r.val.factors.get c).2.length) :
    (finiteGraph G hk r).ports ⟨⟨.inl c,(0 : Fin 1)⟩,j⟩ =
      .inr (.inl ⟨c,j⟩,false) := by
  simp [finiteGraph,FiniteSubstitution.graph,replacement,Network.corolla,
    Raw.incidence,Raw.incidencePorts,Equiv.sigmaAssoc,Equiv.sigmaCongrRight,
    Equiv.sigmaSumDistrib,Equiv.sumCongr,Equiv.sumAssoc,Equiv.sumProdDistrib,
    Equiv.sigmaProdDistrib,Equiv.sumSigmaDistrib,splitEnds,noBoundary]

theorem variable_port (i : Fin r.val.variables) (v : Fin (variableMacro hk r i).shape.vertices)
    (j : Fin ((variableMacro hk r i).shape.arity v)) :
    (finiteGraph G hk r).ports ⟨⟨.inr i,v⟩,j⟩ =
      Sum.elim (fun b => .inr (.inl ((Raw.grouping r).symm ⟨i,b⟩),true))
        (fun e => .inr (.inr ⟨.inr i,e.1⟩,e.2)) ((variableMacro hk r i).shape.ports ⟨v,j⟩) := by
  dsimp [finiteGraph,FiniteSubstitution.graph,replacement,Equiv.trans_apply,
    Equiv.sigmaAssoc,Equiv.sigmaCongrRight,Equiv.sigmaSumDistrib,Equiv.sumCongr,
    Equiv.sumAssoc,Equiv.sumProdDistrib,Equiv.sigmaProdDistrib,Raw.incidence,
    Raw.incidencePorts,Equiv.sumSigmaDistrib,splitEnds,noBoundary]
  generalize hq : (variableMacro hk r i).shape.ports ⟨v,j⟩ = q
  cases q <;> rfl

theorem edgeIndex_boundary_value (i : Fin r.val.variables) (b : Fin (Raw.degree r.val i.val)) :
    (edgeIndex G hk r (.inl ((Raw.grouping r).symm ⟨i,b⟩))).val =
      ComputationLayout.outerOffset r i.val + b.val := by
  rw [edgeIndex_outer_value]
  have hi : Raw.address r.val ((Raw.grouping r).symm ⟨i,b⟩) = i.val := by
    have hv := Raw.grouping_variable r ((Raw.grouping r).symm ⟨i,b⟩)
    rw [(Raw.grouping r).apply_symm_apply] at hv
    exact (congrArg Fin.val hv).symm
  rw [hi,(Raw.grouping r).apply_symm_apply]

end
end Paper2.DegreeCSP.QueryGraph
