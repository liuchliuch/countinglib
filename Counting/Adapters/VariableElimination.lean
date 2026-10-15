import Counting.Integration.RelationalCounting
import Counting.Algorithm.VariableElimination.Bridge
import Counting.Algorithm.VariableElimination.MeasuredOrder
import Counting.Algorithm.VariableEliminationLayout.Program
import Counting.Algorithm.VariableEliminationWork.Inputs

/-!
# Variable elimination computes the shared accepted-witness count

The actual bucket executor computes relation-language instances, with a supplied
order or its canonical order. Boundary values are fixed explicitly and all hidden
variables count, including isolated ones. No polynomial-time or #P-membership
claim is inferred from this executable exact-count specification.
-/

namespace Counting.Adapters.VariableElimination

open Counting.Algorithm.VariableElimination
open Counting.Integration

variable {D H B ι : Type}

/-- Supplied-order elimination counts precisely the satisfying assignments. -/
theorem evaluate_eq_countAccepted [Fintype D] [LinearOrder D]
    [Fintype H] [LinearOrder H] (order : EliminationOrder H)
    (L : RelationLanguage D ι) (I : Counting.Model.OpenInstance L.indicator B H)
    (a : B → D) :
    order.evaluate (pinnedFactors I a) = Counting.Foundation.countAccepted (L.accepts I a) := by
  rw [evaluate_pinnedFactors, L.partition_eq_countAccepted]

/-- The canonical executable computes the same finite accepted count. -/
theorem run_eq_countAccepted [Fintype D] [LinearOrder D]
    [Fintype H] [LinearOrder H] (L : RelationLanguage D ι)
    (I : Counting.Model.OpenInstance L.indicator B H) (a : B → D) :
    EliminationOrder.run (pinnedFactors I a) =
      Counting.Foundation.countAccepted (L.accepts I a) := by
  rw [run_pinnedFactors, L.partition_eq_countAccepted]

/-- The exact Boolean result uses the library's ordered length-n witness convention. -/
theorem run_eq_witnessCount {n : Nat} (L : RelationLanguage Bool ι)
    (I : Counting.Model.OpenInstance L.indicator B (Fin n)) (a : B → Bool) :
    EliminationOrder.run (pinnedFactors I a) =
      Counting.Foundation.witnessCount n (L.acceptsBits I a) := by
  rw [run_pinnedFactors, L.partition_eq_witnessCount]

/-- The instrumented executor returns the witness count while recording its work. -/
theorem measuredRun_eq_witnessCount {n : Nat} (L : RelationLanguage Bool ι)
    (I : Counting.Model.OpenInstance L.indicator B (Fin n)) (a : B → Bool) :
    (EliminationOrder.runMeasured (pinnedFactors I a)).value =
      Counting.Foundation.witnessCount n (L.acceptsBits I a) := by
  rw [EliminationOrder.value_runMeasured, run_eq_witnessCount]


/-- The actual cached Fin executor preserves the public accepted-assignment count.
This is a value theorem, independent of the still separate whole-run cost model. -/
theorem cachedEvaluateFin_eq_countAccepted {q : Nat}
    [Fintype H] [LinearOrder H] (order : EliminationOrder H)
    (L : RelationLanguage (Fin q) ι)
    (I : Counting.Model.OpenInstance L.indicator B H) (a : B → Fin q) :
    Counting.Algorithm.VariableEliminationLayout.evaluateFin order (pinnedFactors I a) =
      Counting.Foundation.countAccepted (L.accepts I a) := by
  rw [Counting.Algorithm.VariableEliminationLayout.evaluateFin_eq_evaluate,
    evaluate_eq_countAccepted]

/-- The canonical cached execution counts all hidden variables, including
isolated ones, over every finite ordinal domain (also the empty domain). -/
theorem cachedRunFin_eq_countAccepted {q : Nat}
    [Fintype H] [LinearOrder H] (L : RelationLanguage (Fin q) ι)
    (I : Counting.Model.OpenInstance L.indicator B H) (a : B → Fin q) :
    Counting.Algorithm.VariableEliminationLayout.runFin (pinnedFactors I a) =
      Counting.Foundation.countAccepted (L.accepts I a) := by
  exact cachedEvaluateFin_eq_countAccepted (EliminationOrder.canonical H) L I a

/-- The observed executor preserves the shared accepted count for semantic inputs.
Each original factor is an explicit oracle callback: its internal work is not
charged by the single oracle-call observation. Stored inputs have a separate API. -/
theorem observedEvaluateFin_eq_countAccepted {q : Nat}
    [Fintype H] [LinearOrder H] (order : EliminationOrder H)
    (L : RelationLanguage (Fin q) ι)
    (I : Counting.Model.OpenInstance L.indicator B H) (a : B → Fin q) :
    (Counting.Algorithm.VariableEliminationWork.evaluate order
      ((pinnedFactors I a).map
        Counting.Algorithm.VariableEliminationWork.ObservedFactor.oracle)).value =
      Counting.Foundation.countAccepted (L.accepts I a) := by
  rw [Counting.Algorithm.VariableEliminationWork.value_evaluate]
  simpa [Counting.Algorithm.VariableEliminationWork.erase, List.map_map,
    Function.comp_def] using
    (partition_pinnedFactors I a).trans (L.partition_eq_countAccepted I a)

end Counting.Adapters.VariableElimination
