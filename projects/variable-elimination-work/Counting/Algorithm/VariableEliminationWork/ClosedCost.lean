import Counting.Algorithm.VariableEliminationWork.Profile

/-! # Preparation and row-materialization formulas for stored readers -/

namespace Counting.Algorithm.VariableEliminationWork

open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableEliminationLayout

variable {V R : Type} {q : Nat}

/-- One actual Fin layout generation, one wrapper, and its installed reader closure. -/
def cachePreparationWork (n q : Nat) : Work :=
  ((Work.ofRange (generateFinRange n).cost).add
    ((Work.ofRange (generateFinRange q).cost).add
      {layoutConstructions := 1, cacheConstructions := 1})).add
    {closureConstructions := 1}

@[simp] theorem work_prepare (f : TabulatedFactor V (Fin q) R) :
    (ObservedFactor.prepare f).work = cachePreparationWork f.arity q := rfl

/-- If all row observations are the same, materialization repeats that actual
observation exactly once per generated row, then prepares one new reader. -/
theorem work_compileRows_const (f : ObservedFactor V (Fin q) R)
    (rows : List (Fin f.arity → Fin q))
    (hrows : rows = enumerateAssignments (Fin f.arity) (Fin q))
    (w : Work) (hw : ∀ a, (f.read a).work = w) :
    (compileRows f rows hrows).work =
      ((Work.scale rows.length w).add
        {listCases := rows.length + 1, arrayPushes := rows.length,
          arrayConstructions := 1}).add (cachePreparationWork f.arity q) := by
  rw [work_compileRows, work_tabulateRows, work_prepare]
  simp only [hw, Work.sum_const]

/-- The generated row list and its real construction costs participate in the
same compile path that materializes and captures the table. -/
theorem work_compile_const (f : ObservedFactor V (Fin q) R)
    (w : Work) (hw : ∀ a, (f.read a).work = w) :
    (compile f).work =
      (Work.ofAssignments (assignmentEnumerationWork f.arity q)).add
        (((Work.scale (q ^ f.arity) w).add
          {listCases := q ^ f.arity + 1, arrayPushes := q ^ f.arity,
            arrayConstructions := 1}).add (cachePreparationWork f.arity q)) := by
  simp only [compile, work_compileRows_const f _ _ w hw, work_enumerateFinAssignments,
    length_values_enumerateFinAssignments]

/-- Closed stored-reader step formula. Retention is still its actual observed
structural recursion; every table/preparation/callback contribution is explicit. -/
def stepWork [Fintype V] [LinearOrder V]
    (v : V) (fs : List (ObservedFactor V (Fin q) R)) : Work :=
  let k := (bucketVars v (erase fs)).length
  (Work.ofRange (generateFinRange q).cost).add
    (((Work.ofAssignments (assignmentEnumerationWork k q)).add
      (((Work.scale (q ^ k) (rowWork q (selected v fs))).add
        {listCases := q ^ k + 1, arrayPushes := q ^ k, arrayConstructions := 1}).add
          (cachePreparationWork k q))).add
      ((retainAll v fs).work.add {listCons := 1, closureConstructions := 1}))

theorem work_step_cached [Fintype V] [LinearOrder V] [CommSemiring R]
    (v : V) (fs : List (ObservedFactor V (Fin q) R)) (h : CachedState fs) :
    (step v fs).work = stepWork v fs := by
  have hw : ∀ a, ((bucketCallback v fs (generateFinRange q).values).read a).work =
      rowWork q (selected v fs) := work_bucketSum_cached v fs h
  simp only [step]
  rw [work_compile_const (bucketCallback v fs (generateFinRange q).values) _ hw]
  rfl

/-- Symbolic closed formulas, evaluated on the scopes/states induced by the
supplied order. No coefficient values or reader counters enter a formula entry. -/
def formulaTrace [CommSemiring R] :
    {V : Type} → [Fintype V] → [LinearOrder V] → EliminationOrder V →
      List (ObservedFactor V (Fin q) R) → List Work
  | _, _, _, .done _, fs => [productWork fs]
  | _, _, _, .step v rest, fs => stepWork v fs :: formulaTrace rest (step v fs).value

theorem work_evaluate_cached [CommSemiring R]
    {V : Type} [finV : Fintype V] [ordV : LinearOrder V]
    (order : EliminationOrder V) (fs : List (ObservedFactor V (Fin q) R))
    (h : CachedState fs) :
    (evaluate order fs).work = Work.sum (formulaTrace order fs) := by
  induction order generalizing finV ordV with
  | done empty => simp [evaluate, formulaTrace, Work.sum, work_endpoint_cached empty fs h]
  | step v rest ih =>
      simp only [evaluate, formulaTrace, Work.sum]
      rw [work_step_cached v fs h, ih _ (cachedState_step v fs h)]

/-- Closed complete stored-input contract. The input preparation is real, once
per occurrence, and the order cost uses the cached-reader invariant it establishes. -/
theorem work_evaluateStored [Fintype V] [LinearOrder V] [CommSemiring R]
    (order : EliminationOrder V) (fs : List (TabulatedFactor V (Fin q) R)) :
    (evaluateStored order fs).work = (prepareInputs fs).work.add
      (Work.sum (formulaTrace order (prepareInputs fs).value)) := by
  simp only [evaluateStored, work_evaluate_cached order _ (cachedState_prepareInputs fs)]

end Counting.Algorithm.VariableEliminationWork
