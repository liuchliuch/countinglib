import Counting.Algorithm.VariableElimination.MeasuredProgram
import Counting.Algorithm.VariableElimination.Order

/-!
# Instrumented execution of complete elimination orders

Each step executes `eliminateMeasured` and recurses on its materialized output.
The empty endpoint executes the product loop over the remaining scalar factors.
The profile records the scopes and bucket occurrence counts arising along this
same order. Its formulas count coefficient additions and multiplications only;
lookup, address calculation, enumeration, allocation, and input callback work are
outside this model.
-/

namespace Counting.Algorithm.VariableElimination
namespace EliminationOrder

variable {V D R : Type}
variable [CommSemiring R] [Fintype D] [LinearOrder D]

/-- Execute and instrument every materialized step and the final scalar product. -/
def evaluateMeasured : {V : Type} → [Fintype V] → [LinearOrder V] →
    EliminationOrder V → List (Factor V D R) → Measured R
  | _, _, _, .done h, fs =>
      Measured.productValues (fs.map (fun f => f.eval (fun v => (h.false v).elim)))
  | _, _, _, .step v rest, fs =>
      let next := eliminateMeasured v fs
      let tail := rest.evaluateMeasured next.value
      ⟨tail.value, next.additions + tail.additions,
        next.multiplications + tail.multiplications⟩

@[simp] theorem value_evaluateMeasured {V : Type}
    [finV : Fintype V] [ordV : LinearOrder V]
    (order : EliminationOrder V) (fs : List (Factor V D R)) :
    (order.evaluateMeasured fs).value = order.evaluate fs := by
  induction order generalizing finV ordV with
  | done h => simp [evaluateMeasured, evaluate, weight]
  | step v rest ih => simp [evaluateMeasured, evaluate, ih]

/-- The measured executable returns the full partition function. -/
theorem evaluateMeasured_eq_partition {V : Type}
    [Fintype V] [LinearOrder V] (order : EliminationOrder V)
    (fs : List (Factor V D R)) :
    (order.evaluateMeasured fs).value = partition fs := by
  rw [value_evaluateMeasured, evaluate_eq_partition]

/-- The actual induced profile: output-scope size and number of incident factor
occurrences at each successive materialized elimination. -/
def scopeTrace : {V : Type} → [Fintype V] → [LinearOrder V] →
    EliminationOrder V → List (Factor V D R) → List (Nat × Nat)
  | _, _, _, .done _, _ => []
  | _, _, _, .step v rest, fs =>
      ((bucketVars v fs).length, (bucket v fs).length) ::
        rest.scopeTrace (eliminate v fs)

/-- The number of scalar factor occurrences multiplied by the endpoint loop. -/
def endpointFactorCount : {V : Type} → [Fintype V] → [LinearOrder V] →
    EliminationOrder V → List (Factor V D R) → Nat
  | _, _, _, .done _, fs => fs.length
  | _, _, _, .step v rest, fs => rest.endpointFactorCount (eliminate v fs)

/-- Every variable contributes exactly one profile entry, including isolated ones. -/
@[simp] theorem length_scopeTrace {V : Type}
    [finV : Fintype V] [ordV : LinearOrder V]
    (order : EliminationOrder V) (fs : List (Factor V D R)) :
    (order.scopeTrace fs).length = order.length := by
  induction order generalizing finV ordV with
  | done h => rfl
  | step v rest ih => simp [scopeTrace, length, ih]

/-- Exact addition count of the recursive executable, expressed in its induced
scope trace. The endpoint product contributes no additions. -/
theorem additions_evaluateMeasured {V : Type}
    [finV : Fintype V] [ordV : LinearOrder V]
    (order : EliminationOrder V) (fs : List (Factor V D R)) :
    (order.evaluateMeasured fs).additions =
      ((order.scopeTrace fs).map
        (fun p => Fintype.card D ^ p.1 * Fintype.card D)).sum := by
  induction order generalizing finV ordV with
  | done h => simp [evaluateMeasured, scopeTrace]
  | step v rest ih => simp [evaluateMeasured, scopeTrace, ih]

/-- Exact multiplication count of the recursive executable. The final term
charges the actual product loop over all remaining scalar occurrences. -/
theorem multiplications_evaluateMeasured {V : Type}
    [finV : Fintype V] [ordV : LinearOrder V]
    (order : EliminationOrder V) (fs : List (Factor V D R)) :
    (order.evaluateMeasured fs).multiplications =
      ((order.scopeTrace fs).map
        (fun p => Fintype.card D ^ p.1 * (Fintype.card D * p.2))).sum +
      order.endpointFactorCount fs := by
  induction order generalizing finV ordV with
  | done h => simp [evaluateMeasured, scopeTrace, endpointFactorCount]
  | step v rest ih => simp [evaluateMeasured, scopeTrace, endpointFactorCount, ih,
      Nat.add_assoc]

/-- Sizes of the materialized arrays, one entry per elimination step. -/
def tableRowTrace [Fintype V] [LinearOrder V]
    (order : EliminationOrder V) (fs : List (Factor V D R)) : List Nat :=
  (order.scopeTrace fs).map (fun p => Fintype.card D ^ p.1)

/-- The trace has one exact table-size entry per variable. -/
@[simp] theorem length_tableRowTrace [Fintype V] [LinearOrder V]
    (order : EliminationOrder V) (fs : List (Factor V D R)) :
    (order.tableRowTrace fs).length = Fintype.card V := by
  simp [tableRowTrace, length_eq_card]

/-- The new table at a step has exactly the first recorded number of rows. -/
theorem tableRowTrace_step [Fintype V] [LinearOrder V]
    (v : V) (rest : EliminationOrder (Remaining v)) (fs : List (Factor V D R)) :
    (EliminationOrder.step v rest).tableRowTrace fs =
      (DenseTable.tabulateMeasured (measuredBucketRow v fs)).value.rowCount ::
        rest.tableRowTrace (eliminate v fs) := by
  simp [tableRowTrace, scopeTrace]

/-- Execute the canonical complete order with arithmetic instrumentation. -/
def runMeasured [Fintype V] [LinearOrder V]
    (fs : List (Factor V D R)) : Measured R := (canonical V).evaluateMeasured fs

@[simp] theorem value_runMeasured [Fintype V] [LinearOrder V]
    (fs : List (Factor V D R)) : (runMeasured fs).value = run fs := by
  simp [runMeasured, run]

/-- Canonical measured execution preserves the partition function. -/
theorem runMeasured_eq_partition [Fintype V] [LinearOrder V]
    (fs : List (Factor V D R)) : (runMeasured fs).value = partition fs := by
  rw [value_runMeasured, run_eq_partition]

end EliminationOrder
end Counting.Algorithm.VariableElimination
