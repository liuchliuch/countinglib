import Counting.Algorithm.VariableEliminationTreewidth.Bridge

/-! # Primal scope graph without changing factor occurrences or ports -/

namespace Counting.Algorithm.VariableEliminationTreewidth
open SimpleGraph
open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableEliminationWidth

variable {V D R : Type} [DecidableEq V]

/-- Two distinct variables are adjacent exactly when some original factor
contains both. This graph projection does not alter the input factor list. -/
def primalGraph (fs : List (Factor V D R)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ f ∈ fs, u ∈ f.support ∧ v ∈ f.support
  symm := ⟨by
    intro u v h
    obtain ⟨hne, f, hf, hu, hv⟩ := h
    exact ⟨hne.symm, f, hf, hv, hu⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

instance primalGraph_decidableAdj (fs : List (Factor V D R)) :
    DecidableRel (primalGraph fs).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ ∃ f ∈ fs, u ∈ f.support ∧ v ∈ f.support))

/-- Distinct-support clique coverage is derived even for repeated ports,
duplicate occurrences, singleton supports and nullary factors. -/
theorem support_isClique (fs : List (Factor V D R)) (f : Factor V D R) (hf : f ∈ fs) :
    (primalGraph fs).IsClique (f.support : Set V) := by
  intro u hu v hv hne
  exact ⟨hne, f, hf, hu, hv⟩

/-- A standard decomposition of the actual primal graph needs no additional
factor-bag witnesses: the Helly-style clique theorem constructs their coverage. -/
theorem bagged_primal {I : Type} [Fintype I] [LinearOrder I]
    {tree : SimpleGraph I} [DecidableRel tree.Adj] {width : Nat}
    (fs : List (Factor V D R)) (d : TreeDecomposition (primalGraph fs) tree width) :
    Bagged d.toDecomposition.bags fs := d.bagged fs (support_isClique fs)

end Counting.Algorithm.VariableEliminationTreewidth
