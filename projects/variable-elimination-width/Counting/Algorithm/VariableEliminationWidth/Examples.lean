import Counting.Algorithm.VariableEliminationWidth.Program
import Counting.Algorithm.VariableElimination.Examples

namespace Counting.Algorithm.VariableEliminationWidth.Examples
open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableElimination.Examples
open Counting.Algorithm.VariableEliminationWork

/-- Two disjoint nontrivial bags plus an isolated vertex. The tree has actual
parent attachments, even though its separators are empty. -/
def sparseBags : Decomposition (Fin 5) 1 where
  bags := [{4}, {0, 1}, {2, 3}]
  tree := .attach {4} (.attach {0, 1} (.root {2, 3}) 0 (by
    intro b hb
    have : b = {2, 3} := by simpa using hb
    subst b
    decide)) 0 (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> decide)
  cover := by decide
  card_le := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> decide

theorem sparse_bagged : Bagged sparseBags.bags sparseNatural := by
  intro f hf
  simp only [sparseNatural, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact ⟨{0, 1}, by decide, by decide⟩
  · exact ⟨{0, 1}, by decide, by decide⟩
  · exact ⟨{2, 3}, by decide, by decide⟩
  · exact ⟨{4}, by decide, by decide⟩

theorem sparse_stored_bagged : Bagged sparseBags.bags
    (tabulatedSparse.map TabulatedFactor.toFactor) := by
  change Bagged sparseBags.bags storedSparse
  rw [storedSparse_eq]
  exact sparse_bagged

theorem sparse_dynamic_width : ScopeBound 1 sparseBags.order sparseNatural :=
  sparseBags.scopeBound _ sparse_bagged

theorem sparse_value : (sparseBags.evaluate tabulatedSparse).value = 360 := by
  rw [Decomposition.value_evaluate]
  change partition storedSparse = 360
  rw [storedSparse_eq, ← EliminationOrder.run_eq_partition, sparseNatural_run]

theorem sparse_rational_value :
    (sparseBags.evaluate (sparseRational.map TabulatedFactor.tabulate)).value = 180 := by
  rw [Decomposition.value_evaluate]
  simp only [List.map_map, TabulatedFactor.toFactor_tabulate, Function.comp_def, List.map_id_fun']
  change partition sparseRational = 180
  rw [← EliminationOrder.run_eq_partition, sparseRational_run]

theorem sparse_rows_bound : (sparseBags.evaluate tabulatedSparse).work.arrayPushes ≤ 10 :=
  sparseBags.rows_le _ sparse_stored_bagged

theorem sparse_additions_bound :
    (sparseBags.evaluate tabulatedSparse).work.coefficientAdditions ≤ 20 :=
  sparseBags.additions_le _ sparse_stored_bagged

/-- A root-only zero-width decomposition. Repeated ports do not increase its width. -/
def singletonBag : Decomposition (Fin 1) 0 where
  bags := [Finset.univ]
  tree := .root Finset.univ
  cover := by
    intro v
    exact ⟨Finset.univ, List.mem_singleton_self _, Finset.mem_univ _⟩
  card_le := by
    intro b hb
    have : b = Finset.univ := by simpa using hb
    subst b
    decide

/-- A loose positive-width certificate exposes the `0^0` empty-domain case:
its isolated pivot still produces one scalar row. -/
def singletonLoose : Decomposition (Fin 1) 1 where
  bags := singletonBag.bags
  tree := singletonBag.tree
  cover := singletonBag.cover
  card_le := by
    intro b hb
    exact (singletonBag.card_le b hb).trans (by decide)

theorem singleton_bagged {D R : Type} (fs : List (Factor (Fin 1) D R)) :
    Bagged singletonBag.bags fs := by
  intro f hf
  exact ⟨Finset.univ, by simp [singletonBag], Finset.subset_univ _⟩

theorem repeated_dynamic_width : ScopeBound 0 singletonBag.order [repeatedScope] :=
  singletonBag.scopeBound _ (singleton_bagged _)

theorem repeated_value :
    (singletonBag.evaluate [TabulatedFactor.tabulate repeatedScope]).value = 4 := by
  rw [Decomposition.value_evaluate]
  simp only [List.map_cons, List.map_nil, TabulatedFactor.toFactor_tabulate]
  decide

/-- Empty root bag, with no variables. Nullary factors and an empty colour domain
still have their single empty row and are evaluated normally. -/
def emptyBag : Decomposition (Fin 0) 0 where
  bags := [∅]
  tree := .root ∅
  cover := fun v => Fin.elim0 v
  card_le := by
    intro b hb
    have : b = ∅ := by simpa using hb
    subst b
    decide

theorem empty_value :
    (emptyBag.evaluate ([] : List (TabulatedFactor (Fin 0) (Fin 0) Nat))).value = 1 := by
  rw [Decomposition.value_evaluate]
  decide

theorem nullary_value :
    (emptyBag.evaluate [TabulatedFactor.tabulate
      (scalarFactor 7 : Factor (Fin 0) (Fin 0) Nat)]).value = 7 := by
  rw [Decomposition.value_evaluate]
  simp only [List.map_cons, List.map_nil, TabulatedFactor.toFactor_tabulate]
  decide

theorem isolated_empty_domain_value :
    (singletonBag.evaluate ([] : List (TabulatedFactor (Fin 1) (Fin 0) Nat))).value = 0 := by
  rw [Decomposition.value_evaluate]
  decide

theorem isolated_singleton_domain_value :
    (singletonBag.evaluate ([] : List (TabulatedFactor (Fin 1) (Fin 1) Nat))).value = 1 := by
  rw [Decomposition.value_evaluate]
  decide

/-- A connected path uses a nonempty separator `{1}`. -/
def pathBags : Decomposition (Fin 3) 1 where
  bags := [{0, 1}, {1, 2}]
  tree := .attach {0, 1} (.root {1, 2}) 0 (by
    intro b hb
    have : b = {1, 2} := by simpa using hb
    subst b
    exact Finset.inter_subset_right)
  cover := by decide
  card_le := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> decide

/-- Three physical ports but only two distinct variables. -/
def repeatedPathEdge : Factor (Fin 3) (Fin 2) Nat where
  arity := 3
  scope := fun i => if i.val = 2 then 1 else 0
  value := fun a => if a 0 = a 2 then 1 else 2

def otherPathEdge : Factor (Fin 3) (Fin 2) Nat where
  arity := 2
  scope := fun i => if i.val = 0 then 1 else 2
  value := fun a => if a 0 = a 1 then 1 else 2

def pathFactors : List (Factor (Fin 3) (Fin 2) Nat) :=
  [repeatedPathEdge, otherPathEdge, scalarFactor 5]

theorem path_bagged : Bagged pathBags.bags pathFactors := by
  intro f hf
  simp only [pathFactors, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact ⟨{0, 1}, by decide, by decide⟩
  · exact ⟨{1, 2}, by decide, by decide⟩
  · exact ⟨{0, 1}, by decide, by decide⟩

theorem path_dynamic_width : ScopeBound 1 pathBags.order pathFactors :=
  pathBags.scopeBound _ path_bagged

theorem path_value :
    (pathBags.evaluate (pathFactors.map TabulatedFactor.tabulate)).value = 90 := by
  rw [Decomposition.value_evaluate]
  simp only [List.map_map, TabulatedFactor.toFactor_tabulate, Function.comp_def, List.map_id_fun']
  decide

#eval do
  unless orderVertices sparseBags.order = [4, 0, 1, 2, 3] do
    throw (IO.userError "Unexpected bag-derived order")
  let result := sparseBags.evaluate tabulatedSparse
  unless result.value = 360 ∧ result.work.arrayPushes = 7 ∧
      result.work.coefficientAdditions = 14 ∧ result.work.coefficientMultiplications = 20 do
    throw (IO.userError "Unexpected bag-derived observed execution")
  unless (sparseBags.evaluate (sparseRational.map TabulatedFactor.tabulate)).value = 180 do
    throw (IO.userError "Unexpected rational bag-derived execution")
  unless orderVertices emptyBag.order = [] ∧ orderVertices singletonBag.order = [0] do
    throw (IO.userError "Unexpected root-only boundary order")
  unless (emptyBag.evaluate ([] : List (TabulatedFactor (Fin 0) (Fin 0) Nat))).value = 1 ∧
      (singletonBag.evaluate ([] : List (TabulatedFactor (Fin 1) (Fin 0) Nat))).value = 0 ∧
      (singletonBag.evaluate ([] : List (TabulatedFactor (Fin 1) (Fin 1) Nat))).value = 1 ∧
      (singletonBag.evaluate [TabulatedFactor.tabulate repeatedScope]).value = 4 do
    throw (IO.userError "Unexpected empty-domain, isolated-variable, or repeated-port result")
  unless (emptyBag.evaluate [TabulatedFactor.tabulate
      (scalarFactor 7 : Factor (Fin 0) (Fin 0) Nat)]).value = 7 do
    throw (IO.userError "Unexpected nullary-only empty-domain execution")
  unless (singletonLoose.evaluate
      ([] : List (TabulatedFactor (Fin 1) (Fin 0) Nat))).work.arrayPushes = 1 do
    throw (IO.userError "Empty-domain nullary row was incorrectly bounded by zero")
  let path := pathBags.evaluate (pathFactors.map TabulatedFactor.tabulate)
  unless orderVertices pathBags.order = [0, 1, 2] ∧ path.value = 90 ∧
      path.work.arrayPushes = 5 ∧ path.work.coefficientAdditions = 10 ∧
      path.work.coefficientMultiplications = 16 ∧ path.work.reads.arrayReads = 16 ∧
      path.work.reads.hornerAdditions = 26 ∧ path.work.reads.coordinateCases = 42 do
    throw (IO.userError "Unexpected nonempty-separator/repeated-port observations")
  IO.println "All supplied bag-tree execution assertions passed."

end Counting.Algorithm.VariableEliminationWidth.Examples
