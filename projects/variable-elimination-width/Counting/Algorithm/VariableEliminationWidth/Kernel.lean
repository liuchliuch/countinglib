import Counting.Algorithm.VariableEliminationWork.Address

/-! # Scalar observations used by the width bounds

These projections are taken from actual observed execution. They deliberately do
not identify the sum of these fields with physical running time.
-/

namespace Counting.Algorithm.VariableEliminationWidth
open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableEliminationWork
open Counting.Algorithm.VariableEliminationLayout

/-- Separate materialization, coefficient and direct-address operation channels. -/
inductive Channel where
  | rows | additions | multiplications | coordinates | hornerAdditions | hornerMultiplications | reads
  deriving DecidableEq, Repr

/-- Project an actual work observation onto one named channel. -/
def Channel.observe : Channel → Work → Nat
  | .rows, w => w.arrayPushes
  | .additions, w => w.coefficientAdditions
  | .multiplications, w => w.coefficientMultiplications
  | .coordinates, w => w.reads.coordinateCases
  | .hornerAdditions, w => w.reads.hornerAdditions
  | .hornerMultiplications, w => w.reads.hornerMultiplications
  | .reads, w => w.reads.arrayReads

@[simp] theorem Channel.observe_add (c : Channel) (x y : Work) :
    c.observe (x.add y) = c.observe x + c.observe y := by cases c <;> rfl
@[simp] theorem Channel.observe_zero (c : Channel) : c.observe Work.zero = 0 := by cases c <;> rfl
@[simp] theorem Channel.observe_scale (c : Channel) (n : Nat) (w : Work) :
    c.observe (Work.scale n w) = n * c.observe w := by cases c <;> rfl

/-- Exact observation for the final occurrence product. Arity is preserved,
including repeated ports; the final empty-variable state forces nullary scopes. -/
def Channel.endpointUnits {V R : Type} {q : Nat} (c : Channel)
    (fs : List (ObservedFactor V (Fin q) R)) : Nat :=
  match c with
  | .rows | .additions => 0
  | .multiplications | .reads => fs.length
  | .coordinates => (fs.map (fun f => f.arity + 1)).sum
  | .hornerAdditions | .hornerMultiplications => (fs.map (fun f => f.arity)).sum

/-- Per-materialized-row units: one output row, `q` additions, or `q` passes
through the selected occurrence readers. No arity bound is assumed. -/
def Channel.rowUnits {V R : Type} {q : Nat} (c : Channel)
    (fs : List (ObservedFactor V (Fin q) R)) : Nat :=
  match c with
  | .rows => 1
  | .additions => q
  | _ => q * c.endpointUnits fs

@[simp] theorem Channel.observe_factorReadWork {V R : Type} {q : Nat} (c : Channel)
    (fs : List (ObservedFactor V (Fin q) R)) :
    c.observe (factorReadWork fs) =
      match c with
      | .rows | .additions | .multiplications => 0
      | .reads => fs.length
      | .coordinates => (fs.map (fun f => f.arity + 1)).sum
      | .hornerAdditions | .hornerMultiplications => (fs.map (fun f => f.arity)).sum := by
  induction fs with
  | nil => cases c <;> rfl
  | cons f fs ih =>
      change c.observe ((cachedReadWork f.arity).add (factorReadWork fs)) = _
      rw [observe_add, ih]
      cases c <;> simp [observe, cachedReadWork, List.sum_cons, Nat.add_comm]

@[simp] theorem Channel.observe_productWork {V R : Type} {q : Nat} (c : Channel)
    (fs : List (ObservedFactor V (Fin q) R)) :
    c.observe (productWork fs) = c.endpointUnits fs := by
  rw [productWork, observe_add, observe_factorReadWork]
  cases c <;> simp [observe, endpointUnits, ReadWork.zero]

@[simp] theorem Channel.observe_retainAll {V R : Type} {q : Nat} [LinearOrder V]
    (c : Channel) (v : V) (fs : List (ObservedFactor V (Fin q) R)) :
    c.observe (retainAll v fs).work = 0 := by
  induction fs with
  | nil => cases c <;> rfl
  | cons f fs ih =>
      simp only [retainAll]
      split <;> rw [observe_add, ih] <;> cases c <;> rfl

@[simp] theorem Channel.observe_preparation (c : Channel) (n q : Nat) :
    c.observe (cachePreparationWork n q) = 0 := by
  cases c <;> rfl

@[simp] theorem Channel.observe_prepareInputs {V R : Type} {q : Nat} (c : Channel)
    (fs : List (TabulatedFactor V (Fin q) R)) : c.observe (prepareInputs fs).work = 0 := by
  induction fs with
  | nil => cases c <;> rfl
  | cons f fs ih =>
      simp only [prepareInputs, observe_add, work_prepare, observe_preparation, ih]
      cases c <;> rfl

/-- All seven observations of one real cached step have the same exponential
row multiplier; the remaining units retain occurrence count and port arities. -/
theorem Channel.observe_step {V R : Type} {q : Nat} [Fintype V] [LinearOrder V]
    [CommSemiring R] (c : Channel) (v : V)
    (fs : List (ObservedFactor V (Fin q) R)) (cached : CachedState fs) :
    c.observe (step v fs).work =
      q ^ (bucketVars v (erase fs)).length * c.rowUnits (selected v fs) := by
  rw [work_step_cached v fs cached]
  simp only [stepWork, observe_add, observe_scale, observe_preparation, observe_retainAll,
    rowWork, observe_productWork]
  cases c <;> simp [observe, Work.ofRange, Work.ofAssignments, rowUnits, endpointUnits,
    ReadWork.zero]

end Counting.Algorithm.VariableEliminationWidth
