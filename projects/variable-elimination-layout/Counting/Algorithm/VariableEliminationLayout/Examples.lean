import Counting.Algorithm.VariableEliminationLayout.Program
import Counting.Algorithm.VariableElimination.Examples

/-!
# Kernel and executable clients of cached layouts

These examples cover genuinely unsorted enumeration inputs, one preparation
shared by multiple reads, exact search increments, arbitrary old arrays, generated
finite-ordinal layouts, empty domains, repeated ports, and rational coefficients.
Kernel equalities and generated-code assertions are separate checks. Whole-order
values below do not assert an unproved whole-execution operation bound.
-/

namespace Counting.Algorithm.VariableEliminationLayout.Examples

open Counting.Algorithm.VariableElimination

open Counting.Algorithm.VariableElimination.Examples

/-- Deliberately noncanonical input, with no sortedness premise. -/
def rawCoordinates : EnumerationSource (Fin 3) :=
  ⟨[2, 0, 1], by decide, by decide⟩

def rawColours : EnumerationSource (Fin 2) :=
  ⟨[1, 0], by decide, by decide⟩

def prepared : LayoutPreparation (Fin 3) (Fin 2) :=
  prepareLayout rawCoordinates rawColours

theorem prepared_coordinates : prepared.layout.coordinates = [0, 1, 2] := by decide
theorem prepared_colours : prepared.layout.colours = [0, 1] := by decide
theorem prepared_coordinateSort : prepared.coordinateSort = ⟨9, 3, 6⟩ := by decide
theorem prepared_colourSort : prepared.colourSort = ⟨6, 1, 3⟩ := by decide

theorem prepared_radix_traversal :
    (prepared.radixTraversal.value, prepared.radixTraversal.listCases,
      prepared.radixTraversal.increments) = (2, 3, 2) := by decide

theorem prepared_one_layout : prepared.layoutConstructions = 1 := rfl

/-- An explicitly supplied array, rather than a newly tabulated function. -/
def oldArray : DenseTable (Fin 3) (Fin 2) Nat :=
  ⟨#[10, 11, 12, 13, 14, 15, 16, 17], by decide⟩

/-- All following reads share this one stored prepared layout. -/
def reusedCache : CachedTable (Fin 3) (Fin 2) Nat := ⟨oldArray, prepared.layout⟩

def low : Fin 3 → Fin 2 := fun _ => 0
def middle : Fin 3 → Fin 2 := fun i => if i = 1 then 1 else 0
def high : Fin 3 → Fin 2 := fun _ => 1

theorem reused_cache_values :
    [reusedCache.eval low, reusedCache.eval middle, reusedCache.eval high] =
      [10, 12, 17] := by decide

theorem reused_cache_fin_values :
    [reusedCache.evalFin low, reusedCache.evalFin middle, reusedCache.evalFin high] =
      [10, 12, 17] := by decide

theorem generic_low_work :
    (reusedCache.read low).work = ⟨4, 3, 3, 0, 3, 3, 1⟩ := by decide

theorem generic_middle_work :
    (reusedCache.read middle).work = ⟨4, 4, 4, 1, 3, 3, 1⟩ := by decide

theorem generic_high_work :
    (reusedCache.read high).work = ⟨4, 6, 6, 3, 3, 3, 1⟩ := by decide

/-- The same tuple has three generic search increments and zero specialized ones. -/
theorem specialized_high_work :
    (reusedCache.readFin high).work = ⟨4, 0, 0, 0, 3, 3, 1⟩ := by decide

/-- Compatibility is not restricted to arrays produced by a tabulator. -/
theorem arbitrary_old_array (t : DenseTable (Fin 3) (Fin 2) ℚ)
    (a : Fin 3 → Fin 2) :
    (CachedTable.mk t prepared.layout).evalFin a = t.eval a := by
  rw [CachedTable.evalFin_eq_eval, CachedTable.eval_eq_legacy]

theorem generated_preparation_cost :
    (prepareFinLayout 3 2).coordinateGeneration = ⟨3, 4, 3, 0, 1⟩ ∧
    (prepareFinLayout 3 2).colourGeneration = ⟨2, 3, 2, 0, 1⟩ ∧
    (prepareFinLayout 3 2).layoutConstructions = 1 := by decide

theorem generated_old_array_read :
    (cacheFinTable oldArray).cache.evalFin middle = 12 := by decide

/-- There is one empty tuple even when its colour domain is empty. -/
def emptyTupleTable : DenseTable (Fin 0) (Fin 0) Nat := ⟨#[7], by decide⟩

theorem empty_tuple_read :
    (cacheFinTable emptyTupleTable).cache.evalFin Fin.elim0 = 7 := by decide

theorem empty_tuple_work :
    ((cacheFinTable emptyTupleTable).cache.readFin Fin.elim0).work =
      ⟨1, 0, 0, 0, 0, 0, 1⟩ := by decide

/-- A nonempty coordinate set over the empty domain instead has no rows. -/
def noRowsTable : DenseTable (Fin 1) (Fin 0) Nat := ⟨#[], by decide⟩

theorem no_rows_cache : (cacheFinTable noRowsTable).cache.table.rowCount = 0 := by decide

theorem no_rows_have_no_assignment (a : Fin 1 → Fin 0) : False := (a 0).elim0

def oneColourTable : DenseTable (Fin 2) (Fin 1) Nat := ⟨#[9], by decide⟩

theorem one_colour_read :
    (cacheFinTable oneColourTable).cache.evalFin (fun _ => 0) = 9 := by decide

theorem one_colour_work :
    ((cacheFinTable oneColourTable).cache.readFin (fun _ => 0)).work =
      ⟨3, 0, 0, 0, 2, 2, 1⟩ := by decide

def rationalArray : DenseTable (Fin 2) (Fin 2) ℚ :=
  ⟨#[1 / 2, 2 / 3, 3 / 4, 5 / 6], by decide⟩

theorem rational_array_read :
    (cacheFinTable rationalArray).cache.evalFin id = 2 / 3 := rfl

/-- Materialization retains both local ports even when their scope repeats. -/
theorem compiled_repeated_arity : (compileFin repeatedScope).arity = 2 := rfl

theorem compiled_repeated_off_diagonal :
    (compileFin repeatedScope).value id = 17 := by
  change (cacheFinTable (DenseTable.tabulate (fun x : Fin 2 → Fin 2 =>
    if x 0 = x 1 then (2 : Nat) else 17))).cache.evalFin id = 17
  rw [evalFin_cacheFinTable, DenseTable.eval_tabulate]
  decide

theorem compiled_repeated_diagonal (a : Fin 1 → Fin 2) :
    (compileFin repeatedScope).eval a = 2 := by
  rw [compileFin_eq]
  simp [Factor.eval, repeatedScope, Function.comp_def]

theorem cached_repeated_run : runFin [repeatedScope] = 4 := by
  rw [runFin_eq_partition]
  decide

theorem cached_empty_domain : runFin ([] : List (Factor (Fin 1) (Fin 0) Nat)) = 0 := by
  rw [runFin_eq_partition]
  decide

theorem cached_empty_variables :
    runFin ([] : List (Factor (Fin 0) (Fin 0) Nat)) = 1 := by
  rw [runFin_eq_partition]
  decide

theorem cached_empty_scalar :
    runFin ([scalarFactor 3] : List (Factor (Fin 0) (Fin 0) Nat)) = 3 := by
  rw [runFin_eq_partition]
  decide

/-- Every generated bucket uses the cached reader, including those of a sparse run. -/
theorem cached_sparse_natural : runFin sparseNatural = 360 := by
  rw [runFin_eq_partition, ← EliminationOrder.run_eq_partition]
  exact sparseNatural_run

theorem cached_sparse_rational : runFin sparseRational = 180 := by
  rw [runFin_eq_partition, ← EliminationOrder.run_eq_partition]
  exact sparseRational_run

theorem cached_isolated_first : evaluateFin isolatedFirst sparseNatural = 360 := by
  rw [evaluateFin_eq_evaluate]
  exact isolatedFirst_run

theorem cached_stored_sparse :
    runFin (tabulatedSparse.map prepareInputFin) = 360 := by
  have h : tabulatedSparse.map prepareInputFin = sparseNatural := by
    calc
      _ = tabulatedSparse.map TabulatedFactor.toFactor := by
        apply List.map_congr_left
        intro f _
        exact prepareInputFin_eq_toFactor f
      _ = sparseNatural := storedSparse_eq
  rw [h, cached_sparse_natural]

/- These assertions exercise generated code, including the actual cached callbacks.
The preceding declarations separately prove the values and local operation counts. -/
#eval do
  let prep := prepareLayout rawCoordinates rawColours
  unless prep.coordinateSort = SortWork.mk 9 3 6 ∧ prep.colourSort = SortWork.mk 6 1 3 do
    throw (IO.userError "Unexpected sort operation counts")
  unless (prep.radixTraversal.value, prep.radixTraversal.listCases,
      prep.radixTraversal.increments, prep.layoutConstructions) = (2, 3, 2, 1) do
    throw (IO.userError "Unexpected radix traversal or preparation count")
  let cache : CachedTable (Fin 3) (Fin 2) Nat := ⟨oldArray, prep.layout⟩
  unless [cache.eval low, cache.eval middle, cache.eval high] = [10, 12, 17] do
    throw (IO.userError "Unexpected reads from a shared generic layout")
  unless [cache.evalFin low, cache.evalFin middle, cache.evalFin high] = [10, 12, 17] do
    throw (IO.userError "Unexpected reads from a shared Fin layout")
  unless (cache.read middle).work = ReadWork.mk 4 4 4 1 3 3 1 ∧
      (cache.read high).work = ReadWork.mk 4 6 6 3 3 3 1 ∧
      (cache.readFin high).work = ReadWork.mk 4 0 0 0 3 3 1 do
    throw (IO.userError "Unexpected generic or specialized read operation counts")
  let generated := cacheFinTable oldArray
  unless generated.cache.evalFin middle = 12 ∧
      generated.preparation.coordinateGeneration = FinRangeCost.mk 3 4 3 0 1 ∧
      generated.preparation.colourGeneration = FinRangeCost.mk 2 3 2 0 1 do
    throw (IO.userError "Unexpected generated layout or cached value")
  unless (cacheFinTable emptyTupleTable).cache.evalFin Fin.elim0 = 7 ∧
      (cacheFinTable noRowsTable).cache.table.rowCount = 0 ∧
      (cacheFinTable oneColourTable).cache.evalFin (fun _ => 0) = 9 ∧
      (cacheFinTable rationalArray).cache.evalFin id = 2 / 3 do
    throw (IO.userError "Unexpected empty, singleton-domain, or rational cached table")
  let repeated := compileFin repeatedScope
  unless repeated.value id = 17 ∧ repeated.eval (fun _ => 1) = 2 ∧
      runFin [repeatedScope] = 4 do
    throw (IO.userError "Repeated ports were not preserved")
  unless runFin ([] : List (Factor (Fin 1) (Fin 0) Nat)) = 0 ∧
      runFin ([] : List (Factor (Fin 0) (Fin 0) Nat)) = 1 ∧
      runFin ([scalarFactor 3] : List (Factor (Fin 0) (Fin 0) Nat)) = 3 do
    throw (IO.userError "Unexpected empty-domain full-order behavior")
  unless runFin sparseNatural = 360 ∧ runFin sparseRational = 180 ∧
      evaluateFin isolatedFirst sparseNatural = 360 ∧
      runFin (tabulatedSparse.map prepareInputFin) = 360 do
    throw (IO.userError "Unexpected sparse cached full-order value")
  IO.println "All cached-layout executable regression assertions passed."

end Counting.Algorithm.VariableEliminationLayout.Examples
