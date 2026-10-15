import Counting.Algorithm.VariableEliminationWidth.Bags
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! # Standard finite graph tree decompositions

The input is a graph tree, its bags, vertex/edge coverage and the usual
path-convex running-intersection property. It contains no root, leaf schedule,
elimination order, factor-bag choices or induced bucket bound.
-/

namespace Counting.Algorithm.VariableEliminationTreewidth

open SimpleGraph

variable {V I : Type} [DecidableEq V]

/-- Running intersection in its unique-tree-path formulation: every vertex in
both endpoint bags belongs to every bag on any simple path between them. -/
def BagConvex (tree : SimpleGraph I) (bag : I → Finset V) : Prop :=
  ∀ (v : V) (i j : I), v ∈ bag i → v ∈ bag j →
    ∀ (p : tree.Walk i j), p.IsPath → ∀ k ∈ p.support, v ∈ bag k

/-- A standard graph tree decomposition with an explicit input width bound.
The finite node representation and decidable adjacency needed by the executable
conversion are supplied as ordinary typeclass instances at that boundary. -/
structure TreeDecomposition (graph : SimpleGraph V) (tree : SimpleGraph I) (width : Nat) where
  isTree : tree.IsTree
  bag : I → Finset V
  cover : ∀ v : V, ∃ i, v ∈ bag i
  edge_cover : ∀ v w : V, graph.Adj v w → ∃ i, v ∈ bag i ∧ w ∈ bag i
  running : BagConvex tree bag
  card_le : ∀ i, (bag i).card ≤ width + 1

omit [DecidableEq V] in
/-- Restricting the graph to an induced node subset preserves path convexity.
The result concerns the actual induced graph, not a newly supplied certificate. -/
theorem BagConvex.induce {tree : SimpleGraph I} {bag : I → Finset V}
    (h : BagConvex tree bag) (s : Set I) :
    BagConvex (tree.induce s) (fun i => bag i.val) := by
  intro v i j hi hj p hp k hk
  let embedding := SimpleGraph.Embedding.induce (G := tree) s
  have mapped : (p.map embedding.toHom).IsPath := hp.map embedding.injective
  have member : embedding k ∈ (p.map embedding.toHom).support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨k, hk, rfl⟩
  exact h v (embedding i) (embedding j) hi hj (p.map embedding.toHom) mapped (embedding k) member

end Counting.Algorithm.VariableEliminationTreewidth
