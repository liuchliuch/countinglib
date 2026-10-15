import Counting.Algorithm.VariableElimination.Bucket
import Counting.Algorithm.VariableElimination.Table

/-!
# Materialized bucket elimination

Semantic input factors expose a value callback. `compileFactor` replaces such a
callback by an array table and may be used at the input boundary. Each elimination
step materializes precisely its new incident-bucket table. Retained factors keep
their existing callback/table without retabulation.
-/

namespace Counting.Algorithm.VariableElimination

variable {V D R : Type} [Fintype V] [LinearOrder V]
variable [Fintype D] [LinearOrder D]

/-- Explicit dense-table input representation. Its list occurrences and ordered
port maps retain duplicate factors and repeated variables. -/
structure TabulatedFactor (V D R : Type) [Fintype D] where
  arity : Nat
  scope : Fin arity → V
  table : DenseTable (Fin arity) D R

namespace TabulatedFactor

/-- Expose an already stored input table to the common semantic factor API. -/
def toFactor (f : TabulatedFactor V D R) : Factor V D R :=
  ⟨f.arity, f.scope, f.table.evalIndexed⟩

/-- Explicitly materialize an input callback before running elimination. Input
construction cost is separate from the elimination arithmetic accounting. -/
def tabulate (f : Factor V D R) : TabulatedFactor V D R :=
  ⟨f.arity, f.scope, DenseTable.tabulate f.value⟩

omit [Fintype V] [LinearOrder V] in
@[simp] theorem toFactor_tabulate (f : Factor V D R) : (tabulate f).toFactor = f := by
  cases f with
  | mk n scope value =>
    dsimp only [tabulate, toFactor]
    congr 1
    funext a
    exact DenseTable.evalIndexed_tabulate value a

end TabulatedFactor

/-- Materialize a factor's finite table. Repeated ports remain distinct table
coordinates; the scope map determines their equality on global assignments. -/
def compileFactor (f : Factor V D R) : Factor V D R :=
  let t := DenseTable.tabulate f.value
  { arity := f.arity, scope := f.scope, value := t.evalIndexed }

omit [Fintype V] [LinearOrder V] in
@[simp] theorem compileFactor_eq (f : Factor V D R) : compileFactor f = f := by
  cases f with
  | mk n scope value =>
    have h : (DenseTable.tabulate value).evalIndexed = value := funext (DenseTable.evalIndexed_tabulate value)
    simpa only [compileFactor] using congrArg (fun value => (⟨n, scope, value⟩ : Factor V D R)) h

/-- Eliminate one specified variable: keep all unrelated factors and materialize
the summed join of exactly the incident factor occurrences. -/
def eliminate [CommSemiring R] (v : V) (fs : List (Factor V D R)) :
    List (Factor (Remaining v) D R) :=
  compileFactor (bucketFactor v fs) :: retained v fs

/-- Exact occurrence count of the residual factor list. -/
theorem length_eliminate [CommSemiring R] (v : V) (fs : List (Factor V D R)) :
    (eliminate v fs).length = (outside v fs).length + 1 := by
  simp [eliminate, retained]

/-- Pointwise marginal correctness of the array-producing step. -/
theorem weight_eliminate [CommSemiring R] (v : V) (fs : List (Factor V D R))
    (a : Remaining v → D) :
    weight (eliminate v fs) a = ∑ d : D, weight fs (extend v d a) := by
  simpa [eliminate] using weight_bucket_elimination v fs a

/-- Partition preservation for the actual materializing executor. -/
theorem partition_eliminate [CommSemiring R] (v : V) (fs : List (Factor V D R)) :
    partition (eliminate v fs) = partition fs := by
  simpa [eliminate] using partition_bucket_elimination v fs

end Counting.Algorithm.VariableElimination
