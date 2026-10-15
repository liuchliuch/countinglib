import Counting.Algorithm.VariableEliminationLayout.FinPreparation
import Counting.Algorithm.VariableElimination.Order
import Counting.Algorithm.VariableElimination.Bridge

/-!
# Actual elimination with cached finite-ordinal readers

Each created table prepares its layout once and captures it in the installed
factor callback. Outside factors retain their callbacks. Every generated table
in this full-order execution uses the Fin-specialized cached reader. Whole-run
operation accounting is a separate obligation from this semantic refinement.
-/

namespace Counting.Algorithm.VariableEliminationLayout

open Counting.Algorithm.VariableElimination

variable {V R : Type} {q : Nat}

/-- Install a cached Fin reader for an existing stored input table. Preparation
is outside the returned callback and therefore is shared by all its reads. -/
def prepareInputFin (f : TabulatedFactor V (Fin q) R) : Factor V (Fin q) R :=
  let cache := (cacheFinTable f.table).cache
  ⟨f.arity, f.scope, cache.evalFin⟩

theorem prepareInputFin_eq_toFactor (f : TabulatedFactor V (Fin q) R) :
    prepareInputFin f = f.toFactor := by
  cases f with
  | mk n scope table =>
      have h : (cacheFinTable table).cache.evalFin = table.evalIndexed := by
        funext a
        rw [CachedTable.evalFin_eq_eval, CachedTable.eval_eq_evalIndexed, table_cacheFinTable]
      exact congrArg (fun value => (⟨n, scope, value⟩ : Factor V (Fin q) R)) h

/-- Materialize a new table and install its cached specialized reader. Repeated
ports remain separate coordinates, exactly as in the original dense table. -/
def compileFin (f : Factor V (Fin q) R) : Factor V (Fin q) R :=
  let table := DenseTable.tabulate f.value
  let cache := (cacheFinTable table).cache
  ⟨f.arity, f.scope, cache.evalFin⟩

@[simp] theorem compileFin_eq (f : Factor V (Fin q) R) : compileFin f = f := by
  cases f with
  | mk n scope value =>
      have h : (cacheFinTable (DenseTable.tabulate value)).cache.evalFin = value := by
        funext a
        rw [evalFin_cacheFinTable, DenseTable.eval_tabulate]
      exact congrArg (fun value => (⟨n, scope, value⟩ : Factor V (Fin q) R)) h

/-- Only the new bucket table is prepared; unrelated factor callbacks are kept. -/
def eliminateFin [Fintype V] [LinearOrder V] [CommSemiring R]
    (v : V) (fs : List (Factor V (Fin q) R)) : List (Factor (Remaining v) (Fin q) R) :=
  compileFin (bucketFactor v fs) :: retained v fs

@[simp] theorem eliminateFin_eq_eliminate [Fintype V] [LinearOrder V] [CommSemiring R]
    (v : V) (fs : List (Factor V (Fin q) R)) : eliminateFin v fs = eliminate v fs := by
  simp [eliminateFin, eliminate]

theorem partition_eliminateFin [Fintype V] [LinearOrder V] [CommSemiring R]
    (v : V) (fs : List (Factor V (Fin q) R)) :
    partition (eliminateFin v fs) = partition fs := by
  rw [eliminateFin_eq_eliminate, partition_eliminate]

/-- Full supplied-order execution keeps the same cached Fin callback path at
every new bucket, and ends by reading and multiplying the scalar factors. -/
def evaluateFin [CommSemiring R] :
    {V : Type} → [Fintype V] → [LinearOrder V] →
      EliminationOrder V → List (Factor V (Fin q) R) → R
  | _, _, _, .done h, fs => weight fs (fun v => (h.false v).elim)
  | _, _, _, .step v rest, fs => evaluateFin rest (eliminateFin v fs)

theorem evaluateFin_eq_partition [CommSemiring R]
    {V : Type} [finV : Fintype V] [ordV : LinearOrder V]
    (order : EliminationOrder V) (fs : List (Factor V (Fin q) R)) :
    evaluateFin order fs = partition fs := by
  induction order generalizing finV ordV with
  | done h =>
      let := h
      simp only [evaluateFin, partition, Fintype.sum_unique]
      exact congrArg (weight fs) (Subsingleton.elim _ _)
  | step v rest ih =>
      rw [evaluateFin, ih]
      exact partition_eliminateFin v fs

theorem evaluateFin_eq_evaluate [CommSemiring R] [Fintype V] [LinearOrder V]
    (order : EliminationOrder V) (fs : List (Factor V (Fin q) R)) :
    evaluateFin order fs = order.evaluate fs := by
  rw [evaluateFin_eq_partition, EliminationOrder.evaluate_eq_partition]

/-- Canonical execution with cached specialized readers for every generated
bucket. Canonical-order construction remains outside preparation/read counters. -/
def runFin [CommSemiring R] [Fintype V] [LinearOrder V]
    (fs : List (Factor V (Fin q) R)) : R := evaluateFin (EliminationOrder.canonical V) fs

@[simp] theorem runFin_eq_partition [CommSemiring R] [Fintype V] [LinearOrder V]
    (fs : List (Factor V (Fin q) R)) : runFin fs = partition fs := evaluateFin_eq_partition _ _

end Counting.Algorithm.VariableEliminationLayout
