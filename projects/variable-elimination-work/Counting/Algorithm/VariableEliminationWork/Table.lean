import Counting.Algorithm.VariableEliminationWork.State
import Counting.Algorithm.VariableEliminationWork.Materialize

/-! # Materialized observed tables with cached readers -/

namespace Counting.Algorithm.VariableEliminationWork

open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableEliminationLayout

variable {V R : Type} {n q : Nat}

/-- Materialize an explicit canonical assignment list. Its generation is supplied
by the caller and is charged by the enclosing executable. The returned array is
exactly the array constructed by the measured push loop. -/
def tabulateRows (reader : (Fin n → Fin q) → Observed R)
    (rows : List (Fin n → Fin q)) (h : rows = enumerateAssignments (Fin n) (Fin q)) :
    Observed (DenseTable (Fin n) (Fin q) R) :=
  let result := materialize reader rows
  ⟨⟨result.value, by simp [result, h]⟩, result.work⟩

@[simp] theorem value_tabulateRows (reader : (Fin n → Fin q) → Observed R)
    (rows : List (Fin n → Fin q)) (h : rows = enumerateAssignments (Fin n) (Fin q)) :
    (tabulateRows reader rows h).value = DenseTable.tabulate (fun a => (reader a).value) := by
  unfold tabulateRows DenseTable.tabulate
  simp [h]

theorem work_tabulateRows (reader : (Fin n → Fin q) → Observed R)
    (rows : List (Fin n → Fin q)) (h : rows = enumerateAssignments (Fin n) (Fin q)) :
    (tabulateRows reader rows h).work =
      (Work.sum (rows.map (fun a => (reader a).work))).add
        {listCases := rows.length + 1, arrayPushes := rows.length, arrayConstructions := 1} :=
  work_materialize reader rows

/-- Execute all observed row callbacks, then prepare one cached specialized
reader for the resulting stored table. No row callback is rerun during a read. -/
def compileRows (f : ObservedFactor V (Fin q) R)
    (rows : List (Fin f.arity → Fin q))
    (h : rows = enumerateAssignments (Fin f.arity) (Fin q)) :
    Observed (ObservedFactor V (Fin q) R) :=
  let table := tabulateRows f.read rows h
  let prepared := ObservedFactor.prepare ⟨f.arity, f.scope, table.value⟩
  ⟨prepared.value, table.work.add prepared.work⟩

@[simp] theorem erase_compileRows (f : ObservedFactor V (Fin q) R)
    (rows : List (Fin f.arity → Fin q))
    (h : rows = enumerateAssignments (Fin f.arity) (Fin q)) :
    (compileRows f rows h).value.erase = f.erase := by
  simp only [compileRows, ObservedFactor.erase_prepare, value_tabulateRows,
    TabulatedFactor.toFactor]
  have he : (DenseTable.tabulate (fun a => (f.read a).value)).evalIndexed =
      fun a => (f.read a).value := by
    funext a
    exact DenseTable.evalIndexed_tabulate _ _
  exact congrArg (fun value => (⟨f.arity, f.scope, value⟩ : Factor V (Fin q) R)) he

/-- Compilation costs contain the actual work returned by every row callback,
array materialization and precisely one cached-layout preparation. -/
theorem work_compileRows (f : ObservedFactor V (Fin q) R)
    (rows : List (Fin f.arity → Fin q))
    (h : rows = enumerateAssignments (Fin f.arity) (Fin q)) :
    (compileRows f rows h).work = (tabulateRows f.read rows h).work.add
      (ObservedFactor.prepare ⟨f.arity, f.scope, (tabulateRows f.read rows h).value⟩).work := rfl

end Counting.Algorithm.VariableEliminationWork
