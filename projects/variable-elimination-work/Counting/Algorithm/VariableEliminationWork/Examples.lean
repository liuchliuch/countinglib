import Counting.Algorithm.VariableEliminationWork.Address
import Counting.Algorithm.VariableElimination.Examples

open Counting.Algorithm.VariableEliminationWork

namespace Counting.Algorithm.VariableEliminationWork.Examples

theorem two_by_two_order :
    ((enumerateFinAssignments 2 2).values.map
      (fun a => [(a 0).val, (a 1).val])) = [[0, 0], [0, 1], [1, 0], [1, 1]] := by
  decide

theorem two_by_two_work :
    (enumerateFinAssignments 2 2).work = ⟨34, 21, 10, 6, 4, 10⟩ := by decide

theorem zero_by_zero_length : (enumerateFinAssignments 0 0).values.length = 1 := by decide

theorem zero_by_zero_work :
    (enumerateFinAssignments 0 0).work = ⟨3, 2, 1, 2, 0, 4⟩ := by decide

theorem one_by_zero_work :
    (enumerateFinAssignments 1 0).work = ⟨4, 2, 0, 3, 1, 5⟩ := by decide

theorem three_by_one_order :
    ((enumerateFinAssignments 3 1).values.map
      (fun a => [(a 0).val, (a 1).val, (a 2).val])) = [[0, 0, 0]] := by decide

theorem three_by_one_work :
    (enumerateFinAssignments 3 1).work = ⟨24, 12, 4, 6, 4, 10⟩ := by decide

#eval do
  let two := enumerateFinAssignments 2 2
  unless two.values.map (fun a : Fin 2 → Fin 2 => [(a 0).val, (a 1).val]) =
      [[0, 0], [0, 1], [1, 0], [1, 1]] do
    throw (IO.userError "Unexpected assignment enumeration order")
  unless two.work = AssignmentWork.mk 34 21 10 6 4 10 do
    throw (IO.userError "Unexpected assignment enumeration observations")
  unless (enumerateFinAssignments 0 0).values.length = 1 ∧
      (enumerateFinAssignments 1 0).values.isEmpty ∧
      (enumerateFinAssignments 3 1).work = AssignmentWork.mk 24 12 4 6 4 10 do
    throw (IO.userError "Unexpected empty or singleton-domain enumeration")
  IO.println "All counted assignment enumeration assertions passed."




open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableElimination.Examples
open Counting.Algorithm.VariableEliminationLayout

theorem stored_sparse_value : (runStored tabulatedSparse).value = 360 := by
  rw [value_runStored]
  change partition storedSparse = 360
  rw [storedSparse_eq, ← EliminationOrder.run_eq_partition, sparseNatural_run]

theorem stored_rational_value :
    (runStored (sparseRational.map TabulatedFactor.tabulate)).value = 180 := by
  rw [value_runStored]
  simp only [List.map_map, TabulatedFactor.toFactor_tabulate, Function.comp_def, List.map_id_fun']
  change partition sparseRational = 180
  rw [← EliminationOrder.run_eq_partition, sparseRational_run]

theorem stored_isolated_first_value :
    (evaluateStored isolatedFirst tabulatedSparse).value = 360 := by
  rw [value_evaluateStored]
  change partition storedSparse = 360
  rw [storedSparse_eq, ← EliminationOrder.run_eq_partition, sparseNatural_run]

theorem stored_repeated_value :
    (runStored [TabulatedFactor.tabulate repeatedScope]).value = 4 := by
  rw [value_runStored]
  simp only [List.map_cons, List.map_nil, TabulatedFactor.toFactor_tabulate]
  decide

theorem no_variables_empty_domain :
    (runStored ([] : List (TabulatedFactor (Fin 0) (Fin 0) Nat))).value = 1 := by
  rw [value_runStored]
  decide

theorem variable_empty_domain :
    (runStored ([] : List (TabulatedFactor (Fin 1) (Fin 0) Nat))).value = 0 := by
  rw [value_runStored]
  decide

def scalarEmpty : TabulatedFactor (Fin 0) (Fin 0) Nat :=
  TabulatedFactor.tabulate (scalarFactor 7)

theorem scalar_empty_domain : (runStored [scalarEmpty]).value = 7 := by
  rw [value_runStored]
  simp only [scalarEmpty, List.map_cons, List.map_nil, TabulatedFactor.toFactor_tabulate]
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem first_stored_address_work :
    (step (0 : Fin 5) (prepareInputs tabulatedSparse).value).work.reads =
      ⟨24, 0, 0, 0, 16, 16, 8⟩ := by
  rw [reads_step_cached _ _ (cachedState_prepareInputs _)]
  have hs : (bucketVars (0 : Fin 5) (erase (prepareInputs tabulatedSparse).value)).length = 1 := by
    rw [erase_prepareInputs]
    change (bucketVars 0 storedSparse).length = 1
    rw [storedSparse_eq]
    exact sparse_first_scope
  simp only [stepAddressProfile, hs]
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem isolated_first_address_work :
    (step (4 : Fin 5) (prepareInputs tabulatedSparse).value).work.reads = ReadWork.zero := by
  rw [reads_step_cached _ _ (cachedState_prepareInputs _)]
  decide

#eval let result := runStored tabulatedSparse; (result.value, result.work)
#eval let result := runStored [TabulatedFactor.tabulate repeatedScope]; (result.value, result.work)
#eval let result := runStored ([] : List (TabulatedFactor (Fin 1) (Fin 0) Nat));
  (result.value, result.work)

#eval do
  let natural := runStored tabulatedSparse
  let rational := runStored (sparseRational.map TabulatedFactor.tabulate)
  unless natural.value = 360 ∧ rational.value = 180 do
    throw (IO.userError "Unexpected observed sparse result")
  unless natural.work.reads = ReadWork.mk 48 0 0 0 28 28 20 ∧
      natural.work.coefficientAdditions = 14 ∧ natural.work.coefficientMultiplications = 20 do
    throw (IO.userError "Unexpected whole-run cached address or coefficient observations")
  unless natural.work.oracleCalls = 0 ∧ natural.work.arrayPushes = 7 ∧
      natural.work.layoutConstructions = 9 ∧ natural.work.cacheConstructions = 9 do
    throw (IO.userError "Unexpected once-only preparation or materialization observations")
  unless (evaluateStored isolatedFirst tabulatedSparse).value = 360 do
    throw (IO.userError "Unexpected supplied-order result")
  let repeated := runStored [TabulatedFactor.tabulate repeatedScope]
  unless repeated.value = 4 ∧ repeated.work.reads = ReadWork.mk 7 0 0 0 4 4 3 do
    throw (IO.userError "Repeated ports lost their independent address contributions")
  unless (runStored ([] : List (TabulatedFactor (Fin 0) (Fin 0) Nat))).value = 1 ∧
      (runStored ([] : List (TabulatedFactor (Fin 1) (Fin 0) Nat))).value = 0 ∧
      (runStored [scalarEmpty]).value = 7 do
    throw (IO.userError "Unexpected zero-variable or empty-domain result")
  IO.println "All observed whole-order regression assertions passed."

end Counting.Algorithm.VariableEliminationWork.Examples
