import Counting.Algorithm.VariableEliminationTreewidth.Primal
import Counting.Algorithm.VariableEliminationTreewidth.RunningIntersection

/-! # Stored-factor execution from a standard primal-graph tree decomposition -/

namespace Counting.Algorithm.VariableEliminationTreewidth
open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableEliminationWidth
open Counting.Algorithm.VariableEliminationWork

variable {V I R : Type} [Fintype V] [LinearOrder V] [Fintype I] [LinearOrder I]
variable {tree : SimpleGraph I} [DecidableRel tree.Adj] {width q : Nat} [CommSemiring R]

/-- Construct both the graph-leaf bag listing and variable-elimination order,
then run the same cached stored-table executor. The supplied decomposition is
of the actual primal graph; no factor-bag witnesses are an input. -/
def evaluate (fs : List (TabulatedFactor V (Fin q) R))
    (d : TreeDecomposition (primalGraph (fs.map TabulatedFactor.toFactor)) tree width) :
    Observed R := d.toDecomposition.evaluate fs

/-- Full finite partition semantics for the actual constructed-order evaluator. -/
@[simp] theorem value_evaluate (fs : List (TabulatedFactor V (Fin q) R))
    (d : TreeDecomposition (primalGraph (fs.map TabulatedFactor.toFactor)) tree width) :
    (evaluate fs d).value = partition (fs.map TabulatedFactor.toFactor) :=
  Decomposition.value_evaluate _ _

/-- The actual variable order induced by the standard decomposition has bounded
buckets, derived through graph clique coverage and the unchanged factor list. -/
theorem scopeBound (fs : List (TabulatedFactor V (Fin q) R))
    (d : TreeDecomposition (primalGraph (fs.map TabulatedFactor.toFactor)) tree width) :
    ScopeBound width d.toDecomposition.order (fs.map TabulatedFactor.toFactor) :=
  d.toDecomposition.scopeBound _ (bagged_primal _ d)

/-- Every channel is read from actual execution. Original occurrence and port
counts remain in the per-row units instead of being replaced by width. -/
theorem observe_evaluate_le (fs : List (TabulatedFactor V (Fin q) R))
    (d : TreeDecomposition (primalGraph (fs.map TabulatedFactor.toFactor)) tree width)
    (c : Channel) :
    c.observe (evaluate fs d).work ≤
      rowCap q width * pivotUnits c d.toDecomposition.order (prepareInputs fs).value +
        finalUnits c d.toDecomposition.order (prepareInputs fs).value :=
  d.toDecomposition.observe_evaluate_le c fs (bagged_primal _ d)

theorem rows_evaluate_le (fs : List (TabulatedFactor V (Fin q) R))
    (d : TreeDecomposition (primalGraph (fs.map TabulatedFactor.toFactor)) tree width) :
    (evaluate fs d).work.arrayPushes ≤ rowCap q width * Fintype.card V :=
  d.toDecomposition.rows_le fs (bagged_primal _ d)

theorem additions_evaluate_le (fs : List (TabulatedFactor V (Fin q) R))
    (d : TreeDecomposition (primalGraph (fs.map TabulatedFactor.toFactor)) tree width) :
    (evaluate fs d).work.coefficientAdditions ≤ rowCap q width * (q * Fintype.card V) :=
  d.toDecomposition.additions_le fs (bagged_primal _ d)

end Counting.Algorithm.VariableEliminationTreewidth
