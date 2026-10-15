import Paper2.DegreeCSP.QueryGraph
import Paper2.DegreeCSP.ComputationLayout

/-! Prefix addresses in the serialized query are exactly the prescribed
finite graph indices. Each occurrence keeps its own filtered-list ordinal. -/
namespace Paper2.DegreeCSP.QueryGraph
open Paper2.Tractable Paper2.ExactInput Paper2.Complexity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem sum_prefix {n : ℕ} (f : Fin n → ℕ) (i : Fin n) :
    (∑ j : Fin n,if j.val < i.val then f j else 0) =
      ∑ j : Fin i.val,f (Fin.castLE i.isLt.le j) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun j _ => Fin.castLE i.isLt.le j)
  · intro j _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_castLE]
    exact j.isLt
  · intro j _ l _ he
    exact Fin.ext (congrArg (fun x : Fin n => x.val) he)
  · intro j hj
    exact ⟨⟨j.val,(Finset.mem_filter.mp hj).2⟩,Finset.mem_univ _,Fin.ext rfl⟩
  · intro j _
    rfl

variable {s : ℕ} {a : ℕ → ℕ} {k : ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (hk : 3 ≤ k) (r : Raw.Input s a k)

theorem macro_vertices (i : Fin r.val.variables) :
    (variableMacro hk r i).shape.vertices = ComputationLayout.vertexCount k (Raw.degree r.val i.val) := by
  exact EqualityDegreeTemplates.make_vertices _ _ _ _

theorem macro_edges (i : Fin r.val.variables) :
    (variableMacro hk r i).shape.edges = ComputationLayout.internalCount k (Raw.degree r.val i.val) := by
  exact EqualityDegreeTemplates.make_edges _ _ _ _

theorem outerIndex_value (p : Raw.Ports r.val) :
    (outerIndex r p).val = ComputationLayout.outerOffset r (Raw.address r.val p) +
      (Raw.grouping r p).2.val := by
  change (finSigmaFinEquiv (n := fun i => Raw.degree r.val i.val) (Raw.grouping r p)).val = _
  rw [finSigmaFinEquiv_apply]
  have hs := sum_prefix (fun i : Fin r.val.variables => Raw.degree r.val i.val) (Raw.grouping r p).1
  exact congrArg (fun q => q + (Raw.grouping r p).2.val) hs.symm

theorem edgeIndex_outer_value (p : Raw.Ports r.val) :
    (edgeIndex G hk r (.inl p)).val = ComputationLayout.outerOffset r (Raw.address r.val p) +
      (Raw.grouping r p).2.val := by
  change (outerIndex r p).val = _
  exact outerIndex_value r p

theorem edgeIndex_inner_value (i : Fin r.val.variables) (e : Fin (variableMacro hk r i).shape.edges) :
    (edgeIndex G hk r (.inr ⟨.inr i,e⟩)).val = ComputationLayout.innerOffset r i.val + e.val := by
  change occurrenceCount r + (finSigmaFinEquiv
    (n := fun i => (variableMacro hk r i).shape.edges) ⟨i,e⟩).val = _
  rw [finSigmaFinEquiv_apply]
  have hs := sum_prefix (fun i : Fin r.val.variables => (variableMacro hk r i).shape.edges) i
  calc
    _ = occurrenceCount r + ((∑ j : Fin r.val.variables,
        if j.val < i.val then (variableMacro hk r j).shape.edges else 0) + e.val) :=
      congrArg (fun q => occurrenceCount r + (q + e.val)) hs.symm
    _ = _ := by
      simp only [macro_edges,ComputationLayout.innerOffset]
      exact (Nat.add_assoc _ _ _).symm

theorem edgeCount_layout : edgeCount hk r = ComputationLayout.edgeCount r := by
  unfold edgeCount innerCount
  simp only [macro_edges]
  rfl

end
end Paper2.DegreeCSP.QueryGraph
