import Counting.Algorithm.VariableEliminationWork.State

/-! # Observed retention of unrelated occurrence readers -/

namespace Counting.Algorithm.VariableEliminationWork

open Counting.Algorithm.VariableElimination

variable {V D R : Type} [LinearOrder V]

/-- Retention executes one source-list case per occurrence, and constructs a
result cons and relabeling closure only for unrelated occurrences. Support
membership is a separate structural query, not charged as a scalar operation. -/
def retainAll (v : V) : List (ObservedFactor V D R) → Observed (List (ObservedFactor (Remaining v) D R))
  | [] => ⟨[], {listCases := 1, nilResults := 1}⟩
  | f :: fs =>
      let tail := retainAll v fs
      if h : v ∈ f.erase.support then
        ⟨tail.value, tail.work.add {listCases := 1}⟩
      else
        ⟨f.retain v h :: tail.value,
          tail.work.add {listCases := 1, listCons := 1, closureConstructions := 1}⟩

@[simp] theorem erase_retainAll [Fintype V] (v : V) (fs : List (ObservedFactor V D R)) :
    erase (retainAll v fs).value = retained v (erase fs) := by
  induction fs with
  | nil => simp [retainAll, erase, retained, outside]
  | cons f fs ih =>
      change erase (retainAll v (f :: fs)).value = retained v (f.erase :: erase fs)
      by_cases h : v ∈ f.erase.support
      · simp only [retainAll, h, dite_true]
        rw [ih]
        simp only [retained, outside, List.attach_filter, List.attach_cons,
          List.map_filterMap, List.filterMap_cons, List.filterMap_map, Function.comp_def]
        simp [h]
        simp only [List.map_filterMap]
        congr 1
        funext x
        split <;> rfl
      · simp only [retainAll, h, dite_false, erase, List.map_cons, ObservedFactor.erase_retain]
        change _ :: erase (retainAll v fs).value = _
        rw [ih]
        simp only [retained, outside, List.attach_filter, List.attach_cons,
          List.map_filterMap, List.filterMap_cons, List.filterMap_map, Function.comp_def]
        simp [h]
        simp only [List.map_filterMap]
        congr 1
        funext x
        split <;> rfl

/-- Retention never executes a coefficient reader. -/
@[simp] theorem reads_retainAll (v : V) (fs : List (ObservedFactor V D R)) :
    (retainAll v fs).work.reads = Counting.Algorithm.VariableEliminationLayout.ReadWork.zero := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      simp only [retainAll]
      split <;> simp only [Work.add, ih] <;> rfl

end Counting.Algorithm.VariableEliminationWork
