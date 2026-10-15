import Counting.Algorithm.VariableEliminationWork.ClosedCost

/-! # Exact cached-address work over a supplied complete order -/

namespace Counting.Algorithm.VariableEliminationWork

open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableEliminationLayout

variable {V R : Type} {q : Nat}

@[simp] theorem readWork_zero_add (w : ReadWork) : ReadWork.zero.add w = w := by
  cases w; simp [ReadWork.zero, ReadWork.add]

@[simp] theorem readWork_add_zero (w : ReadWork) : w.add ReadWork.zero = w := by
  cases w; rfl

/-- One read from every occurrence, preserving repeated ports. -/
def factorAddressProfile (fs : List (ObservedFactor V (Fin q) R)) : ReadWork :=
  ⟨(fs.map (fun f => f.arity + 1)).sum, 0, 0, 0,
    (fs.map (fun f => f.arity)).sum, (fs.map (fun f => f.arity)).sum, fs.length⟩

/-- The induced output scope supplies `q^k` rows; each row evaluates each incident
occurrence at all `q` pivot colours. Outside readers contribute zero to this step. -/
def stepAddressProfile [Fintype V] [LinearOrder V]
    (v : V) (fs : List (ObservedFactor V (Fin q) R)) : ReadWork :=
  let k := (bucketVars v (erase fs)).length
  let bs := selected v fs
  ⟨q ^ k * (q * (bs.map (fun f => f.arity + 1)).sum), 0, 0, 0,
    q ^ k * (q * (bs.map (fun f => f.arity)).sum),
    q ^ k * (q * (bs.map (fun f => f.arity)).sum), q ^ k * (q * bs.length)⟩

@[simp] theorem reads_stepWork [Fintype V] [LinearOrder V]
    (v : V) (fs : List (ObservedFactor V (Fin q) R)) :
    (stepWork v fs).reads = stepAddressProfile v fs := by
  simp [stepWork, stepAddressProfile, Work.add, Work.scale, Work.ofRange,
    Work.ofAssignments, cachePreparationWork, reads_retainAll, reads_rowWork,
    ReadWork.add, ReadWork.zero]

theorem reads_step_cached [Fintype V] [LinearOrder V] [CommSemiring R]
    (v : V) (fs : List (ObservedFactor V (Fin q) R)) (h : CachedState fs) :
    (step v fs).work.reads = stepAddressProfile v fs := by
  rw [work_step_cached v fs h, reads_stepWork]

/-- Symbolic address contributions along the actual induced states, including
one final scalar-reader profile. Explicit evaluation of this specification is
separate from executing the observed program. -/
def addressTrace [CommSemiring R] :
    {V : Type} → [Fintype V] → [LinearOrder V] → EliminationOrder V →
      List (ObservedFactor V (Fin q) R) → List ReadWork
  | _, _, _, .done _, fs => [factorAddressProfile fs]
  | _, _, _, .step v rest, fs =>
      stepAddressProfile v fs :: addressTrace rest (step v fs).value

theorem reads_evaluate_cached [CommSemiring R]
    {V : Type} [finV : Fintype V] [ordV : LinearOrder V]
    (order : EliminationOrder V) (fs : List (ObservedFactor V (Fin q) R))
    (h : CachedState fs) :
    (evaluate order fs).work.reads = ReadWork.sum (addressTrace order fs) := by
  induction order generalizing finV ordV with
  | done empty =>
      simp only [evaluate, work_endpoint_cached empty fs h, reads_productWork,
        addressTrace, ReadWork.sum, readWork_add_zero, factorAddressProfile]
  | step v rest ih =>
      simp only [evaluate, Work.add, addressTrace, ReadWork.sum]
      rw [reads_step_cached v fs h, ih _ (cachedState_step v fs h)]

@[simp] theorem reads_prepareInputs (fs : List (TabulatedFactor V (Fin q) R)) :
    (prepareInputs fs).work.reads = ReadWork.zero := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      simp [prepareInputs, Work.add, ih, work_prepare, cachePreparationWork,
        Work.ofRange, ReadWork.add, ReadWork.zero]

/-- No cached-state premise is required at the stored-table boundary. Every
read in the complete run is accounted for by the induced address profile. -/
theorem reads_evaluateStored [Fintype V] [LinearOrder V] [CommSemiring R]
    (order : EliminationOrder V) (fs : List (TabulatedFactor V (Fin q) R)) :
    (evaluateStored order fs).work.reads =
      ReadWork.sum (addressTrace order (prepareInputs fs).value) := by
  simp only [evaluateStored, Work.add, reads_prepareInputs, readWork_zero_add,
    reads_evaluate_cached order _ (cachedState_prepareInputs fs)]

end Counting.Algorithm.VariableEliminationWork
