import Counting.Algorithm.VariableEliminationTreewidth.Standard

/-! # Degree-one graph leaves and their bag separators -/

namespace Counting.Algorithm.VariableEliminationTreewidth
open SimpleGraph

variable {V I : Type} [DecidableEq V] [Fintype I] [LinearOrder I]

/-- The actual unique neighbour of a finite degree-one node, chosen by a finite
minimum operation. This is executable and introduces no choice of elimination order. -/
def leafParent (tree : SimpleGraph I) [DecidableRel tree.Adj] (leaf : I)
    (degree : tree.degree leaf = 1) : I :=
  (tree.neighborFinset leaf).min' (by
    apply Finset.card_pos.mp
    change 0 < tree.degree leaf
    omega)

theorem leafParent_adj (tree : SimpleGraph I) [DecidableRel tree.Adj] (leaf : I)
    (degree : tree.degree leaf = 1) : tree.Adj leaf (leafParent tree leaf degree) := by
  apply (tree.mem_neighborFinset leaf _).mp
  exact Finset.min'_mem _ _

/-- All old occurrences of a leaf-bag vertex lie through its unique neighbour.
This derives precisely the local overlap premise required by the frozen D3 API. -/
theorem leaf_separator {tree : SimpleGraph I} [DecidableRel tree.Adj]
    (isTree : tree.IsTree) {bag : I → Finset V} (running : BagConvex tree bag)
    (leaf : I) (degree : tree.degree leaf = 1) (other : I) (different : other ≠ leaf) :
    bag leaf ∩ bag other ⊆ bag (leafParent tree leaf degree) := by
  intro v hv
  obtain ⟨hvleaf, hvother⟩ := Finset.mem_inter.mp hv
  obtain ⟨parent, hadj, unique⟩ := degree_eq_one_iff_existsUnique_adj.mp degree
  have hp : leafParent tree leaf degree = parent := unique _ (leafParent_adj tree leaf degree)
  obtain ⟨path, hpath⟩ := isTree.connected.exists_isPath leaf other
  cases path with
  | nil => exact False.elim (different rfl)
  | @cons start middle finish adjacent tail =>
      have hn : middle = parent := unique _ adjacent
      apply running v leaf other hvleaf hvother (.cons adjacent tail) hpath
        (leafParent tree leaf degree)
      rw [hp, ← hn]
      exact List.mem_cons_of_mem _ tail.start_mem_support

omit [LinearOrder I] in
/-- Removing the chosen leaf yields another actual graph tree. -/
theorem isTree_remove_leaf {tree : SimpleGraph I} [DecidableRel tree.Adj]
    (isTree : tree.IsTree) (leaf : I) (degree : tree.degree leaf = 1) :
    (tree.induce {leaf}ᶜ).IsTree :=
  ⟨isTree.connected.induce_compl_singleton_of_degree_eq_one degree, isTree.isAcyclic.induce _⟩

end Counting.Algorithm.VariableEliminationTreewidth
