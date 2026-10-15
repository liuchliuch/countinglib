import Counting.Algorithm.VariableEliminationTreewidth.Program
import Counting.Algorithm.VariableEliminationWidth.Examples

namespace Counting.Algorithm.VariableEliminationTreewidth.Examples
open SimpleGraph
open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableElimination.Examples
open Counting.Algorithm.VariableEliminationWidth
open Counting.Algorithm.VariableEliminationWork

/-- Two adjacent graph nodes are supplied, without a root or removal schedule. -/
theorem twoNodes_tree : (⊤ : SimpleGraph (Fin 2)).IsTree := by
  exact ⟨SimpleGraph.connected_top, SimpleGraph.IsAcyclic.of_card_le_two (by simp)⟩

/-- Every bag assignment on this two-node tree satisfies running intersection:
its induced occurrence subgraphs are complete graphs. -/
theorem twoNodes_running {V : Type} (bag : Fin 2 → Finset V) :
    BagConvex (⊤ : SimpleGraph (Fin 2)) bag := by
  apply BagConvex.of_occurrence_preconnected twoNodes_tree
  intro v
  rw [SimpleGraph.induce_top]
  exact SimpleGraph.preconnected_top

abbrev pathFactors := Counting.Algorithm.VariableEliminationWidth.Examples.pathFactors

def pathTables : List (TabulatedFactor (Fin 3) (Fin 2) Nat) :=
  pathFactors.map TabulatedFactor.tabulate

/-- Standard edge coverage supplies the two bags; no clique or factor witness is
required. The first factor has three ports but only two distinct variables. -/
def pathDecomposition : TreeDecomposition
    (primalGraph (pathTables.map TabulatedFactor.toFactor)) (⊤ : SimpleGraph (Fin 2)) 1 where
  isTree := twoNodes_tree
  bag := fun i => if i.val = 0 then {0, 1} else {1, 2}
  cover := by decide
  edge_cover := by decide
  running := twoNodes_running _
  card_le := by decide

theorem path_scopeBound :
    ScopeBound 1 pathDecomposition.toDecomposition.order (pathTables.map TabulatedFactor.toFactor) :=
  scopeBound pathTables pathDecomposition

theorem path_value : (evaluate pathTables pathDecomposition).value = 90 := by
  rw [value_evaluate]
  have h := Counting.Algorithm.VariableEliminationWidth.Examples.path_value
  rw [Decomposition.value_evaluate] at h
  exact h

theorem path_rows_bound : (evaluate pathTables pathDecomposition).work.arrayPushes ≤ 6 :=
  rows_evaluate_le pathTables pathDecomposition

instance pathGraphDecidableAdj (n : Nat) : DecidableRel (SimpleGraph.pathGraph n).Adj := by
  intro u v
  change Decidable (u ⋖ v ∨ v ⋖ u)
  unfold CovBy
  infer_instance

/-- Three-node graph regression exercises two successive graph-leaf deletions. -/
theorem threeNodes_tree : (SimpleGraph.pathGraph 3).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨SimpleGraph.pathGraph_connected 2, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  decide

def sparseBagFunction (i : Fin 3) : Finset (Fin 5) :=
  if i.val = 0 then {4} else if i.val = 1 then {0, 1} else {2, 3}

def sparseDecomposition : TreeDecomposition
    (primalGraph (tabulatedSparse.map TabulatedFactor.toFactor)) (SimpleGraph.pathGraph 3) 1 where
  isTree := threeNodes_tree
  bag := sparseBagFunction
  cover := by decide
  edge_cover := by decide
  running := by
    apply BagConvex.of_occurrence_preconnected threeNodes_tree
    intro v i j
    have unique : ∀ (v : Fin 5) (i j : Fin 3),
        v ∈ sparseBagFunction i → v ∈ sparseBagFunction j → i = j := by decide
    have same : i = j := Subtype.ext (unique v i.val j.val i.property j.property)
    subst j
    exact SimpleGraph.Reachable.rfl
  card_le := by decide

theorem sparse_value : (evaluate tabulatedSparse sparseDecomposition).value = 360 := by
  rw [value_evaluate]
  change partition storedSparse = 360
  rw [storedSparse_eq, ← EliminationOrder.run_eq_partition, sparseNatural_run]

/-- A conventional singleton node graph gives the ordinary one-bag decomposition
for any finite graph, including no variables and isolated vertices. -/
def rootDecomposition {V : Type} [Fintype V] [DecidableEq V] (graph : SimpleGraph V)
    (width : Nat) (bound : Fintype.card V ≤ width + 1) :
    TreeDecomposition graph (⊥ : SimpleGraph (Fin 1)) width where
  isTree := SimpleGraph.IsTree.of_subsingleton
  bag := fun _ => Finset.univ
  cover := fun v => ⟨0, Finset.mem_univ v⟩
  edge_cover := fun v w _ => ⟨0, Finset.mem_univ v, Finset.mem_univ w⟩
  running := by intro v i j hi hj p hp k hk; exact Finset.mem_univ v
  card_le := fun _ => by simpa using bound

def rationalTables : List (TabulatedFactor (Fin 5) (Fin 2) ℚ) :=
  sparseRational.map TabulatedFactor.tabulate

def rationalDecomposition :=
  rootDecomposition (primalGraph (rationalTables.map TabulatedFactor.toFactor)) 4 (by decide)

theorem rational_value : (evaluate rationalTables rationalDecomposition).value = 180 := by
  rw [value_evaluate]
  simp only [rationalTables, List.map_map, TabulatedFactor.toFactor_tabulate,
    Function.comp_def, List.map_id_fun']
  change partition sparseRational = 180
  rw [← EliminationOrder.run_eq_partition, sparseRational_run]

def emptyTables : List (TabulatedFactor (Fin 0) (Fin 0) Nat) := []
def emptyDecomposition := rootDecomposition (primalGraph
  (emptyTables.map TabulatedFactor.toFactor)) 0 (by decide)

def scalarTables : List (TabulatedFactor (Fin 0) (Fin 0) Nat) :=
  [TabulatedFactor.tabulate (scalarFactor 7)]
def scalarDecomposition := rootDecomposition (primalGraph
  (scalarTables.map TabulatedFactor.toFactor)) 0 (by decide)

def isolatedTables (q : Nat) : List (TabulatedFactor (Fin 1) (Fin q) Nat) := []
def isolatedDecomposition (q : Nat) := rootDecomposition (primalGraph
  ((isolatedTables q).map TabulatedFactor.toFactor)) 1 (by decide)

theorem empty_value : (evaluate emptyTables emptyDecomposition).value = 1 := by
  rw [value_evaluate]
  decide

theorem scalar_value : (evaluate scalarTables scalarDecomposition).value = 7 := by
  rw [value_evaluate]
  simp only [scalarTables, List.map_cons, List.map_nil, TabulatedFactor.toFactor_tabulate]
  decide

theorem isolated_empty_value : (evaluate (isolatedTables 0) (isolatedDecomposition 0)).value = 0 := by
  rw [value_evaluate]
  decide

theorem isolated_singleton_value : (evaluate (isolatedTables 1) (isolatedDecomposition 1)).value = 1 := by
  rw [value_evaluate]
  decide

#eval do
  unless pathDecomposition.listing.nodes = [0, 1] ∧
      orderVertices pathDecomposition.toDecomposition.order = [0, 1, 2] do
    throw (IO.userError "Unexpected graph-derived bag listing or variable order")
  unless sparseDecomposition.listing.nodes = [0, 1, 2] ∧
      orderVertices sparseDecomposition.toDecomposition.order = [4, 0, 1, 2, 3] ∧
      (evaluate tabulatedSparse sparseDecomposition).value = 360 do
    throw (IO.userError "Unexpected three-node tree/duplicate-factor/isolated-variable execution")
  let path := evaluate pathTables pathDecomposition
  unless path.value = 90 ∧ path.work.arrayPushes = 5 ∧
      path.work.coefficientAdditions = 10 ∧ path.work.coefficientMultiplications = 16 ∧
      path.work.reads.arrayReads = 16 ∧ path.work.reads.hornerAdditions = 26 do
    throw (IO.userError "Unexpected standard decomposition execution observations")
  unless (evaluate rationalTables rationalDecomposition).value = 180 ∧
      (evaluate emptyTables emptyDecomposition).value = 1 ∧
      (evaluate scalarTables scalarDecomposition).value = 7 ∧
      (evaluate (isolatedTables 0) (isolatedDecomposition 0)).value = 0 ∧
      (evaluate (isolatedTables 1) (isolatedDecomposition 1)).value = 1 do
    throw (IO.userError "Unexpected standard decomposition boundary client")
  unless (evaluate (isolatedTables 0) (isolatedDecomposition 0)).work.arrayPushes = 1 do
    throw (IO.userError "Empty-domain scalar row lost during graph conversion")
  IO.println "All standard tree-decomposition execution assertions passed."

end Counting.Algorithm.VariableEliminationTreewidth.Examples
