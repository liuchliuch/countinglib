import Counting.Algorithm.VariableEliminationWork.Program

/-! # Stored input boundary with once-only layout preparation -/

namespace Counting.Algorithm.VariableEliminationWork

open Counting.Algorithm.VariableElimination

variable {V R : Type} {q : Nat}

/-- Prepare each stored input occurrence once. Duplicate occurrences and repeated
ports retain their own state, and no stored coefficient is evaluated here. -/
def prepareInputs : List (TabulatedFactor V (Fin q) R) → Observed (List (ObservedFactor V (Fin q) R))
  | [] => ⟨[], {listCases := 1, nilResults := 1}⟩
  | f :: fs =>
      let first := ObservedFactor.prepare f
      let tail := prepareInputs fs
      ⟨first.value :: tail.value,
        first.work.add (tail.work.add {listCases := 1, listCons := 1})⟩

@[simp] theorem erase_prepareInputs (fs : List (TabulatedFactor V (Fin q) R)) :
    erase (prepareInputs fs).value = fs.map TabulatedFactor.toFactor := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      simpa [prepareInputs, erase] using congrArg (fun xs => f.toFactor :: xs) ih

/-- End-to-end stored-table evaluator. Initial preparation and every later
callback observation are retained in the returned work, including the endpoint. -/
def evaluateStored [Fintype V] [LinearOrder V] [CommSemiring R]
    (order : EliminationOrder V) (fs : List (TabulatedFactor V (Fin q) R)) : Observed R :=
  let prepared := prepareInputs fs
  let execution := evaluate order prepared.value
  ⟨execution.value, prepared.work.add execution.work⟩

@[simp] theorem value_evaluateStored [Fintype V] [LinearOrder V] [CommSemiring R]
    (order : EliminationOrder V) (fs : List (TabulatedFactor V (Fin q) R)) :
    (evaluateStored order fs).value = partition (fs.map TabulatedFactor.toFactor) := by
  simp only [evaluateStored, value_evaluate, erase_prepareInputs]

/-- The supplied input tables are treated as input data. This constructor also
executes canonical-order construction, which is outside the work observations. -/
def runStored [Fintype V] [LinearOrder V] [CommSemiring R]
    (fs : List (TabulatedFactor V (Fin q) R)) : Observed R :=
  evaluateStored (EliminationOrder.canonical V) fs

@[simp] theorem value_runStored [Fintype V] [LinearOrder V] [CommSemiring R]
    (fs : List (TabulatedFactor V (Fin q) R)) :
    (runStored fs).value = partition (fs.map TabulatedFactor.toFactor) :=
  value_evaluateStored _ _

end Counting.Algorithm.VariableEliminationWork
