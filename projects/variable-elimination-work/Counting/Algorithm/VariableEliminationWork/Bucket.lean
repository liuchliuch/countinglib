import Counting.Algorithm.VariableEliminationWork.State

/-! # Actual bucket callback loops with retained work -/

namespace Counting.Algorithm.VariableEliminationWork

open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableEliminationLayout

variable {V R : Type} {q : Nat}
variable [Fintype V] [LinearOrder V] [CommSemiring R]

/-- Execute each incident occurrence's own observed callback on one pivot row. -/
def bucketProduct (v : V) (fs : List (ObservedFactor V (Fin q) R))
    (d : Fin q) (a : Fin (bucketVars v (erase fs)).length → Fin q) : Observed R :=
  Observed.product (fun f : {f // f ∈ selected v fs} =>
    f.val.read (bucketRow v (erase fs) d a (semanticMember v fs f))) (selected v fs).attach

@[simp] theorem value_bucketProduct (v : V) (fs : List (ObservedFactor V (Fin q) R))
    (d : Fin q) (a : Fin (bucketVars v (erase fs)).length → Fin q) :
    (bucketProduct v fs d a).value =
      ((bucket v (erase fs)).attach.map (fun f =>
        f.val.value (bucketRow v (erase fs) d a f))).prod := by
  rw [bucketProduct, Observed.value_product, attach_bucket]
  simp only [List.map_map, Function.comp_def, semanticMember, ObservedFactor.erase]

/-- The colour list is supplied once by the table constructor. Every pivot
coefficient sum executes the same measured product callbacks. -/
def bucketSum (v : V) (fs : List (ObservedFactor V (Fin q) R))
    (colours : List (Fin q))
    (a : Fin (bucketVars v (erase fs)).length → Fin q) : Observed R :=
  Observed.sum (fun d => bucketProduct v fs d a) colours

@[simp] theorem value_bucketSum (v : V) (fs : List (ObservedFactor V (Fin q) R))
    (a : Fin (bucketVars v (erase fs)).length → Fin q) :
    (bucketSum v fs (generateFinRange q).values a).value =
      (bucketFactor v (erase fs)).value a := by
  simp only [bucketSum, Observed.value_sum, value_bucketProduct]
  rw [generateFinRange_values]
  simpa only [enumerateValues, Fin.sort_univ, bucketFactor] using
    (sum_enumerateValues (fun d : Fin q =>
      ((bucket v (erase fs)).attach.map (fun f =>
        f.val.value (bucketRow v (erase fs) d a f))).prod))

/-- The complete callback contribution of one actual incident-product loop. -/
theorem work_bucketProduct (v : V) (fs : List (ObservedFactor V (Fin q) R))
    (d : Fin q) (a : Fin (bucketVars v (erase fs)).length → Fin q) :
    (bucketProduct v fs d a).work =
      (Work.sum ((selected v fs).attach.map (fun f =>
        (f.val.read (bucketRow v (erase fs) d a (semanticMember v fs f))).work))).add
      {coefficientMultiplications := (selected v fs).length,
       listCases := (selected v fs).length + 1} := by
  rw [bucketProduct, Observed.work_product, List.length_attach]

theorem work_bucketSum (v : V) (fs : List (ObservedFactor V (Fin q) R))
    (colours : List (Fin q)) (a : Fin (bucketVars v (erase fs)).length → Fin q) :
    (bucketSum v fs colours a).work =
      (Work.sum (colours.map (fun d => (bucketProduct v fs d a).work))).add
        {coefficientAdditions := colours.length, listCases := colours.length + 1} :=
  Observed.work_sum _ _

end Counting.Algorithm.VariableEliminationWork
