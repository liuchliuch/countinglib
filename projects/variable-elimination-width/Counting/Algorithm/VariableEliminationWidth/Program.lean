import Counting.Algorithm.VariableEliminationWidth.Bounds

/-! # Public evaluator selected by a supplied bag tree -/

namespace Counting.Algorithm.VariableEliminationWidth
open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableEliminationWork

variable {V R : Type} {q width : Nat} [Fintype V] [LinearOrder V] [CommSemiring R]

/-- Construct the order from the supplied bag tree and invoke the actual cached
stored-table executor. Order construction and decomposition checking are outside
its returned execution-work observations. -/
def Decomposition.evaluate (d : Decomposition V width)
    (fs : List (TabulatedFactor V (Fin q) R)) : Observed R := evaluateStored d.order fs

@[simp] theorem Decomposition.value_evaluate (d : Decomposition V width)
    (fs : List (TabulatedFactor V (Fin q) R)) :
    (d.evaluate fs).value = partition (fs.map TabulatedFactor.toFactor) :=
  value_evaluateStored _ _

/-- Finite input bags imply the width bound for the actual installed executor. -/
theorem Decomposition.observe_evaluate_le (d : Decomposition V width) (c : Channel)
    (fs : List (TabulatedFactor V (Fin q) R))
    (covered : Bagged d.bags (fs.map TabulatedFactor.toFactor)) :
    c.observe (d.evaluate fs).work ≤
      rowCap q width * pivotUnits c d.order (prepareInputs fs).value +
        finalUnits c d.order (prepareInputs fs).value := d.observe_evaluateStored_le c fs covered

/-- Positive domain specialization of the width exponential. This premise is
about simplifying the numeric bound; the executor itself accepts empty domains. -/
theorem Decomposition.observe_evaluate_le_of_pos (d : Decomposition V width) (c : Channel)
    (fs : List (TabulatedFactor V (Fin q) R)) (positive : 0 < q)
    (covered : Bagged d.bags (fs.map TabulatedFactor.toFactor)) :
    c.observe (d.evaluate fs).work ≤
      q ^ width * pivotUnits c d.order (prepareInputs fs).value +
        finalUnits c d.order (prepareInputs fs).value := by
  simpa only [rowCap_of_pos positive] using d.observe_evaluate_le c fs covered

/-- Read the actual dependent order as a list of original vertices. -/
def orderVertices : {V : Type} → EliminationOrder V → List V
  | _, .done _ => []
  | _, .step v rest => v :: (orderVertices rest).map Subtype.val

end Counting.Algorithm.VariableEliminationWidth
