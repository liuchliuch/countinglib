import Counting.Algorithm.VariableEliminationWork.Bucket
import Counting.Algorithm.VariableEliminationWork.Retain
import Counting.Algorithm.VariableEliminationWork.Table
import Counting.Algorithm.VariableEliminationWork.Enumeration
import Counting.Algorithm.VariableElimination.Order

/-!
# Whole-order execution retaining callback and preparation observations

The executor itself invokes observed factor callbacks. It records their returned
work during each bucket product and endpoint product, then composes these with
coefficient, enumeration, array-push and cached-layout preparation observations.
Structural support/scope queries and applications of supplied assignment functions
remain distinct from this logical operation model; no bit-time bound is asserted.
-/

namespace Counting.Algorithm.VariableEliminationWork

open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableEliminationLayout

variable {V R : Type} {q : Nat}

def Work.ofAssignments (w : AssignmentWork) : Work where
  listCases := w.listCases
  listCons := w.listCons
  closureConstructions := w.assignmentClosures
  generationTests := w.rangeTests
  natIncrements := w.natIncrements
  nilResults := w.nilResults

/-- Generate the actual canonical row list, execute its callbacks, materialize
its array, and install one cached specialized reader. -/
def compile (f : ObservedFactor V (Fin q) R) : Observed (ObservedFactor V (Fin q) R) :=
  let rows := enumerateFinAssignments f.arity q
  let result := compileRows f rows.values (values_enumerateFinAssignments f.arity q)
  ⟨result.value, (Work.ofAssignments rows.work).add result.work⟩

@[simp] theorem erase_compile (f : ObservedFactor V (Fin q) R) :
    (compile f).value.erase = f.erase := by
  simp only [compile, erase_compileRows]

/-- An observed row callback retains every incident factor's returned work. -/
def bucketCallback [Fintype V] [LinearOrder V] [CommSemiring R]
    (v : V) (fs : List (ObservedFactor V (Fin q) R)) (colours : List (Fin q)) :
    ObservedFactor (Remaining v) (Fin q) R :=
  ⟨(bucketVars v (erase fs)).length, (bucketVars v (erase fs)).get,
    bucketSum v fs colours⟩

@[simp] theorem erase_bucketCallback [Fintype V] [LinearOrder V] [CommSemiring R]
    (v : V) (fs : List (ObservedFactor V (Fin q) R)) :
    (bucketCallback v fs (generateFinRange q).values).erase = bucketFactor v (erase fs) := by
  have h : (fun a => (bucketSum v fs (generateFinRange q).values a).value) =
      (bucketFactor v (erase fs)).value := by
    funext a
    exact value_bucketSum v fs a
  exact congrArg (fun value =>
    (⟨(bucketVars v (erase fs)).length, (bucketVars v (erase fs)).get, value⟩ :
      Factor (Remaining v) (Fin q) R)) h

/-- Compile exactly one incident bucket, keep unrelated observed callbacks, and
combine the work those actual executions return. Pivot colours are generated
once per table, outside the callback captured by the row loop. -/
def step [Fintype V] [LinearOrder V] [CommSemiring R]
    (v : V) (fs : List (ObservedFactor V (Fin q) R)) :
    Observed (List (ObservedFactor (Remaining v) (Fin q) R)) :=
  let colours := generateFinRange q
  let compiled := compile (bucketCallback v fs colours.values)
  let rest := retainAll v fs
  ⟨compiled.value :: rest.value,
    (Work.ofRange colours.cost).add (compiled.work.add
      (rest.work.add {listCons := 1, closureConstructions := 1}))⟩

@[simp] theorem erase_step [Fintype V] [LinearOrder V] [CommSemiring R]
    (v : V) (fs : List (ObservedFactor V (Fin q) R)) :
    erase (step v fs).value = Counting.Algorithm.VariableElimination.eliminate v (erase fs) := by
  simp only [step, erase, List.map_cons, erase_compile, erase_bucketCallback]
  change bucketFactor v (erase fs) :: erase (retainAll v fs).value = _
  rw [erase_retainAll]
  simp only [Counting.Algorithm.VariableElimination.eliminate, compileFactor_eq]
  rfl

theorem partition_step [Fintype V] [LinearOrder V] [CommSemiring R]
    (v : V) (fs : List (ObservedFactor V (Fin q) R)) :
    partition (erase (step v fs).value) = partition (erase fs) := by
  rw [erase_step, partition_eliminate]

/-- Execute the final scalar product through the very same observed readers. -/
def endpoint [MulOneClass R] (h : IsEmpty V) (fs : List (ObservedFactor V (Fin q) R)) :
    Observed R :=
  Observed.product (fun f => f.read (fun i => (h.false (f.scope i)).elim)) fs

@[simp] theorem value_endpoint [CommMonoid R]
    (h : IsEmpty V) (fs : List (ObservedFactor V (Fin q) R)) :
    (endpoint h fs).value = weight (erase fs) (fun v => (h.false v).elim) := by
  simp only [endpoint, Observed.value_product, weight, erase, List.map_map,
    Factor.eval, ObservedFactor.erase, Function.comp_def]

/-- Actual complete-order recursion; every step's returned observations are
retained, and the endpoint invokes all remaining scalar callbacks. -/
def evaluate [CommSemiring R] :
    {V : Type} → [Fintype V] → [LinearOrder V] → EliminationOrder V →
      List (ObservedFactor V (Fin q) R) → Observed R
  | _, _, _, .done h, fs => endpoint h fs
  | _, _, _, .step v rest, fs =>
      let next := step v fs
      let tail := evaluate rest next.value
      ⟨tail.value, next.work.add tail.work⟩

@[simp] theorem value_evaluate [CommSemiring R]
    {V : Type} [finV : Fintype V] [ordV : LinearOrder V]
    (order : EliminationOrder V) (fs : List (ObservedFactor V (Fin q) R)) :
    (evaluate order fs).value = partition (erase fs) := by
  induction order generalizing finV ordV with
  | done h =>
      let := h
      rw [evaluate, value_endpoint]
      simp only [partition, Fintype.sum_unique]
      exact congrArg (weight (erase fs)) (Subsingleton.elim _ _)
  | step v rest ih =>
      rw [evaluate, ih]
      exact partition_step v fs

/-- Work from the actual executions, in supplied-order sequence, with an endpoint
entry. This trace records operations; it does not assert an optimal order. -/
def workTrace [CommSemiring R] :
    {V : Type} → [Fintype V] → [LinearOrder V] → EliminationOrder V →
      List (ObservedFactor V (Fin q) R) → List Work
  | _, _, _, .done h, fs => [(endpoint h fs).work]
  | _, _, _, .step v rest, fs =>
      let next := step v fs
      next.work :: workTrace rest next.value

theorem work_evaluate [CommSemiring R]
    {V : Type} [finV : Fintype V] [ordV : LinearOrder V]
    (order : EliminationOrder V) (fs : List (ObservedFactor V (Fin q) R)) :
    (evaluate order fs).work = Work.sum (workTrace order fs) := by
  induction order generalizing finV ordV with
  | done h => simp [evaluate, workTrace, Work.sum]
  | step v rest ih => simp [evaluate, workTrace, Work.sum, ih]

end Counting.Algorithm.VariableEliminationWork
