import Counting.Algorithm.VariableEliminationTreewidth.Linearize
import Counting.Algorithm.VariableEliminationTreewidth.Clique
import Counting.Algorithm.VariableEliminationWidth.Program

/-! # From a standard graph decomposition to actual width-bounded execution -/

namespace Counting.Algorithm.VariableEliminationTreewidth
open SimpleGraph
open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableEliminationWidth
open Counting.Algorithm.VariableEliminationWork

variable {V I : Type} [DecidableEq V] [Fintype I] [LinearOrder I]
variable {graph : SimpleGraph V} {tree : SimpleGraph I} [DecidableRel tree.Adj] {width : Nat}

/-- Execute finite graph-leaf conversion on the supplied decomposition's actual
node graph; the list and its parent indices are computed rather than assumed. -/
def TreeDecomposition.listing (d : TreeDecomposition graph tree width) : BagListing d.bag :=
  linearize tree d.isTree d.bag d.running

/-- Convert unchanged original bags into the certified parent-attachment API.
The output's variable and size fields follow from ordinary vertex coverage. -/
def TreeDecomposition.toDecomposition (d : TreeDecomposition graph tree width) :
    Decomposition V width where
  bags := d.listing.nodes.map d.bag
  tree := d.listing.tree
  cover := by
    intro v
    obtain ⟨i, hi⟩ := d.cover v
    exact ⟨d.bag i, List.mem_map.mpr ⟨i, d.listing.complete i, rfl⟩, hi⟩
  card_le := by
    intro bag hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact d.card_le i

/-- Graph edge coverage survives the actual node listing. -/
theorem TreeDecomposition.edge_cover_converted (d : TreeDecomposition graph tree width)
    (u v : V) (h : graph.Adj u v) :
    ∃ bag ∈ d.toDecomposition.bags, u ∈ bag ∧ v ∈ bag := by
  obtain ⟨i, hu, hv⟩ := d.edge_cover u v h
  exact ⟨d.bag i, List.mem_map.mpr ⟨i, d.listing.complete i, rfl⟩, hu, hv⟩

/-- Standard graph coverage and running intersection imply clique containment;
the executable conversion does not ask the caller for a containing bag. -/
theorem TreeDecomposition.clique_covered (d : TreeDecomposition graph tree width)
    (s : Finset V) (clique : graph.IsClique (s : Set V)) :
    ∃ bag ∈ d.toDecomposition.bags, s ⊆ bag :=
  clique_subset_bag d.toDecomposition.tree graph d.toDecomposition.cover
    d.edge_cover_converted s clique

/-- Every factor whose distinct support is a graph clique is covered after the
conversion, with every occurrence and port still present in the original list. -/
theorem TreeDecomposition.bagged {D R : Type} (d : TreeDecomposition graph tree width)
    (fs : List (Factor V D R))
    (cliques : ∀ f ∈ fs, graph.IsClique (f.support : Set V)) :
    Bagged d.toDecomposition.bags fs := fun f hf => d.clique_covered f.support (cliques f hf)

end Counting.Algorithm.VariableEliminationTreewidth
