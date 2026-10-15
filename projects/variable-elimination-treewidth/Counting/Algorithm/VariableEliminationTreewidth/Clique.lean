import Counting.Algorithm.VariableEliminationWidth.Bags
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Finite clique containment from local bag-tree intersections

For a supplied leaf-attachment `BagTree`, pairwise coverage of a finite set by
the bags implies coverage by a single bag. The proof uses the actual stored
parent and its local overlap condition. It assumes neither global clique
containment nor factor-bag containment. Vertex and edge coverage then give the
usual graph-clique consequence, including empty and singleton cliques.
-/

namespace Counting.Algorithm.VariableEliminationTreewidth

open Counting.Algorithm.VariableEliminationWidth

variable {V : Type} [DecidableEq V]

/-- Finite pairwise bag coverage implies containment in one bag. Pairs include
equal vertices, so this hypothesis also records coverage of singleton sets. The
bag tree has a root, and consequently the conclusion also holds for `s = ∅`. -/
theorem pairwise_covered_subset_bag {bags : List (Finset V)}
    (tree : BagTree bags) (s : Finset V)
    (pair_cover : ∀ u ∈ s, ∀ v ∈ s, ∃ bag ∈ bags, u ∈ bag ∧ v ∈ bag) :
    ∃ bag ∈ bags, s ⊆ bag := by
  revert pair_cover
  induction tree with
  | root bag =>
      intro pair_cover
      refine ⟨bag, by simp, ?_⟩
      intro u hu
      obtain ⟨other, ho, huo, _⟩ := pair_cover u hu u hu
      have same : other = bag := by simpa using ho
      simpa [same] using huo
  | @attach bag bags rest parent overlap ih =>
      intro pair_cover
      by_cases in_leaf : s ⊆ bag
      · exact ⟨bag, by simp, in_leaf⟩
      · obtain ⟨z, hzs, hz_leaf⟩ := Finset.not_subset.mp in_leaf
        have in_parent : ∀ u ∈ s, u ∈ bag → u ∈ bags.get parent := by
          intro u hu hu_leaf
          obtain ⟨other, ho, hu_other, hz_other⟩ := pair_cover u hu z hzs
          rcases List.mem_cons.mp ho with same | ho
          · subst other
            exact False.elim (hz_leaf hz_other)
          · exact overlap other ho (Finset.mem_inter.mpr ⟨hu_leaf, hu_other⟩)
        have tail_cover : ∀ u ∈ s, ∀ v ∈ s,
            ∃ other ∈ bags, u ∈ other ∧ v ∈ other := by
          intro u hu v hv
          obtain ⟨other, ho, hu_other, hv_other⟩ := pair_cover u hu v hv
          rcases List.mem_cons.mp ho with same | ho
          · subst other
            exact ⟨bags.get parent, List.get_mem _ _,
              in_parent u hu hu_other, in_parent v hv hv_other⟩
          · exact ⟨other, ho, hu_other, hv_other⟩
        obtain ⟨other, ho, contained⟩ := ih tail_cover
        exact ⟨other, List.mem_cons_of_mem _ ho, contained⟩

/-- Vertex and edge coverage of a graph imply that each of its finite cliques
is contained in one bag of the supplied bag tree. The vertex-coverage premise
handles equal vertices without assuming an edge loop. -/
theorem clique_subset_bag {bags : List (Finset V)} (tree : BagTree bags)
    (graph : SimpleGraph V)
    (cover : ∀ v : V, ∃ bag ∈ bags, v ∈ bag)
    (edge_cover : ∀ u v : V, graph.Adj u v → ∃ bag ∈ bags, u ∈ bag ∧ v ∈ bag)
    (s : Finset V) (clique : graph.IsClique (s : Set V)) :
    ∃ bag ∈ bags, s ⊆ bag := by
  apply pairwise_covered_subset_bag tree s
  intro u hu v hv
  by_cases same : u = v
  · subst v
    obtain ⟨bag, hb, hub⟩ := cover u
    exact ⟨bag, hb, hub, hub⟩
  · exact edge_cover u v (clique hu hv same)

/-- The width bound on input bags bounds every finite graph clique after
clique containment has been derived; it is not a clique-containment premise. -/
theorem clique_card_le {width : Nat} (d : Decomposition V width)
    (graph : SimpleGraph V)
    (edge_cover : ∀ u v : V,
      graph.Adj u v → ∃ bag ∈ d.bags, u ∈ bag ∧ v ∈ bag)
    (s : Finset V) (clique : graph.IsClique (s : Set V)) :
    s.card ≤ width + 1 := by
  obtain ⟨bag, hb, contained⟩ := clique_subset_bag d.tree graph d.cover edge_cover s clique
  exact (Finset.card_le_card contained).trans (d.card_le bag hb)

end Counting.Algorithm.VariableEliminationTreewidth
