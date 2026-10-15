import Counting.Algorithm.VariableEliminationTreewidth.Listing

/-! # Executable conversion of a supplied finite graph tree

The algorithm searches the actual degree-one vertices, removes the least leaf,
and recurses on the actual induced graph. A leaf-free tree is proved to be a
singleton. Neither a root nor a leaf-deletion schedule is supplied by the user.
-/

namespace Counting.Algorithm.VariableEliminationTreewidth
open SimpleGraph

/-- Convert a finite graph tree and path-convex bags to the frozen parent-index
representation. Runtime choices are finite minima and list searches. -/
def linearize {V I : Type} [DecidableEq V] [Fintype I] [LinearOrder I]
    (tree : SimpleGraph I) [DecidableRel tree.Adj] (isTree : tree.IsTree)
    (bag : I → Finset V) (running : BagConvex tree bag) : BagListing bag :=
  let leaves := (Finset.univ : Finset I).filter (fun i => tree.degree i = 1)
  if h : leaves.Nonempty then
    let leaf := leaves.min' h
    have degree : tree.degree leaf = 1 := (Finset.mem_filter.mp (Finset.min'_mem leaves h)).2
    let rest := linearize (tree.induce {leaf}ᶜ) (isTree_remove_leaf isTree leaf degree)
      (fun i => bag i.val) (running.induce {leaf}ᶜ)
    let parent := leafParent tree leaf degree
    have parent_ne : parent ≠ leaf := (leafParent_adj tree leaf degree).ne'
    rest.attach bag leaf ⟨parent, parent_ne⟩ (fun i => leaf_separator isTree running leaf degree i.val i.property)
  else
    have singleton : Subsingleton I := by
      classical
      by_contra hs
      have : Nontrivial I := not_subsingleton_iff_nontrivial.mp hs
      obtain ⟨i, hi⟩ := isTree.exists_vert_degree_one_of_nontrivial
      exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    letI := singleton
    let root := (Finset.univ : Finset I).min' (Finset.univ_nonempty_iff.mpr isTree.connected.nonempty)
    BagListing.singleton bag root
termination_by Fintype.card I
  decreasing_by
    exact Fintype.card_subtype_lt (p := fun i => i ≠ leaf) (x := leaf) (by simp)

end Counting.Algorithm.VariableEliminationTreewidth
