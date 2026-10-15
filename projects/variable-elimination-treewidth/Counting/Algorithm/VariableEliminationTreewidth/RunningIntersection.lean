import Counting.Algorithm.VariableEliminationTreewidth.Standard

/-! # Equivalence with connected vertex-occurrence subgraphs -/

namespace Counting.Algorithm.VariableEliminationTreewidth
open SimpleGraph

variable {V I : Type} {tree : SimpleGraph I} {bag : I → Finset V}

/-- Connectedness of the bags containing each vertex implies the unique-path
formulation of running intersection on a tree. -/
theorem BagConvex.of_occurrence_preconnected (isTree : tree.IsTree)
    (connected : ∀ v : V, (tree.induce {i | v ∈ bag i}).Preconnected) :
    BagConvex tree bag := by
  intro v i j hi hj p hp k hk
  obtain ⟨inside, hins⟩ := (connected v).exists_isPath ⟨i, hi⟩ ⟨j, hj⟩
  let embedding := SimpleGraph.Embedding.induce (G := tree) {i | v ∈ bag i}
  let mapped : tree.Walk i j := inside.map embedding.toHom
  have hmapped : mapped.IsPath := hins.map embedding.injective
  have same : p = mapped := congrArg Subtype.val
    ((isTree.isAcyclic.subsingleton_path i j).elim ⟨p, hp⟩ ⟨mapped, hmapped⟩)
  rw [same] at hk
  change k ∈ (inside.map embedding.toHom).support at hk
  rw [SimpleGraph.Walk.support_map] at hk
  obtain ⟨node, hnode, heq⟩ := List.mem_map.mp hk
  have heq' : node.val = k := heq
  rw [← heq']
  exact node.property

/-- The path-convex form also gives connectedness of every nonempty occurrence
subgraph; using Preconnected allows missing vertices without an extra premise. -/
theorem BagConvex.occurrence_preconnected (isTree : tree.IsTree)
    (running : BagConvex tree bag) (v : V) :
    (tree.induce {i | v ∈ bag i}).Preconnected := by
  intro i j
  obtain ⟨p, hp⟩ := isTree.connected.exists_isPath i.val j.val
  have contained : ∀ k ∈ p.support, k ∈ {i | v ∈ bag i} :=
    running v i.val j.val i.property j.property p hp
  exact (p.induce {i | v ∈ bag i} contained).reachable

/-- Either standard running-intersection formulation can supply the executable
conversion; the path form is not an extra hypothesis on top of connected bags. -/
theorem bagConvex_iff_occurrence_preconnected (isTree : tree.IsTree) :
    BagConvex tree bag ↔ ∀ v : V, (tree.induce {i | v ∈ bag i}).Preconnected :=
  ⟨fun h v => h.occurrence_preconnected isTree v,
    fun h => BagConvex.of_occurrence_preconnected isTree h⟩

end Counting.Algorithm.VariableEliminationTreewidth
