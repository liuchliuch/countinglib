import Counting.Algorithm.VariableEliminationLayout.Batch
import Counting.Algorithm.VariableEliminationLayout.Examples

/-! # One-preparation batch regression clients -/

namespace Counting.Algorithm.VariableEliminationLayout.BatchExamples

open Examples

def assignments : List (Fin 3 → Fin 2) := [low, middle, high]

theorem generic_batch_values :
    (reusedCache.readMany assignments).values = [10, 12, 17] := by decide

theorem generic_batch_work :
    (reusedCache.readMany assignments).reads = ⟨12, 13, 13, 4, 9, 9, 3⟩ := by decide

theorem fin_batch_work :
    (reusedCache.readManyFin assignments).reads = ⟨12, 0, 0, 0, 9, 9, 3⟩ := by
  simpa [assignments] using CachedTable.reads_readManyFin reusedCache assignments

theorem once_prepared_values :
    (prepareReadManyFin oldArray assignments).batch.values = [10, 12, 17] := by decide

theorem once_prepared_generation :
    (prepareReadManyFin oldArray assignments).preparation.preparation.coordinateGeneration =
      ⟨3, 4, 3, 0, 1⟩ ∧
    (prepareReadManyFin oldArray assignments).preparation.preparation.colourGeneration =
      ⟨2, 3, 2, 0, 1⟩ := by simp

theorem once_prepared_batch_work :
    (prepareReadManyFin oldArray assignments).batch.reads = ⟨12, 0, 0, 0, 9, 9, 3⟩ := by
  simpa [assignments] using reads_prepareReadManyFin oldArray assignments

theorem batch_own_constructions :
    (prepareReadManyFin oldArray assignments).batch.assignmentListCases = 4 ∧
    (prepareReadManyFin oldArray assignments).batch.outputCons = 3 := by decide

#eval do
  let generic := reusedCache.readMany assignments
  unless generic.values == [10, 12, 17] &&
      generic.reads == (⟨12, 13, 13, 4, 9, 9, 3⟩ : ReadWork) do
    throw (IO.userError "Generic cached batch changed")
  let prepared := prepareReadManyFin oldArray assignments
  unless prepared.batch.values == [10, 12, 17] &&
      prepared.batch.reads == (⟨12, 0, 0, 0, 9, 9, 3⟩ : ReadWork) &&
      prepared.preparation.preparation.coordinateGeneration == (⟨3, 4, 3, 0, 1⟩ : FinRangeCost) &&
      prepared.preparation.preparation.colourGeneration == (⟨2, 3, 2, 0, 1⟩ : FinRangeCost) &&
      prepared.batch.assignmentListCases == 4 && prepared.batch.outputCons == 3 do
    throw (IO.userError "One-preparation Fin batch changed")
  IO.println "All once-prepared batch regression assertions passed."

end Counting.Algorithm.VariableEliminationLayout.BatchExamples
