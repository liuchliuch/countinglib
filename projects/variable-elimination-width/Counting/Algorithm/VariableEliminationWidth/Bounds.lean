import Counting.Algorithm.VariableEliminationWidth.Invariant
import Counting.Algorithm.VariableEliminationWidth.Kernel

/-! # Width-dependent bounds for actual complete cached execution -/

namespace Counting.Algorithm.VariableEliminationWidth
open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableEliminationWork

variable {R : Type} {q : Nat} [CommSemiring R]

/-- Accumulate per-row units on the actual induced observed states. This retains
occurrence multiplicity and original port arities independently of width. -/
def pivotUnits (c : Channel) : {V : Type} → [Fintype V] → [LinearOrder V] →
    EliminationOrder V → List (ObservedFactor V (Fin q) R) → Nat
  | _, _, _, .done _, _ => 0
  | _, _, _, .step v rest, fs =>
      c.rowUnits (selected v fs) + pivotUnits c rest (step v fs).value

/-- The final product contribution, without an unnecessary exponential factor. -/
def finalUnits (c : Channel) : {V : Type} → [Fintype V] → [LinearOrder V] →
    EliminationOrder V → List (ObservedFactor V (Fin q) R) → Nat
  | _, _, _, .done _, fs => c.endpointUnits fs
  | _, _, _, .step v rest, fs => finalUnits c rest (step v fs).value

/-- The cap is valid also when `q = 0`, where replacing every `0^k` by `0^width`
would be false for a generated nullary table. -/
def rowCap (q width : Nat) : Nat := (max 1 q) ^ width

theorem pow_le_rowCap {k width q : Nat} (h : k ≤ width) : q ^ k ≤ rowCap q width := by
  calc
    q ^ k ≤ (max 1 q) ^ k := Nat.pow_le_pow_left (le_max_right _ _) _
    _ ≤ (max 1 q) ^ width := Nat.pow_le_pow_right (by omega) h

theorem rowCap_of_pos {q : Nat} (h : 0 < q) (width : Nat) : rowCap q width = q ^ width := by
  simp [rowCap, max_eq_right (by omega : 1 ≤ q)]

/-- Complete-run bound on actual returned observations. ScopeBound refers to
old semantic states; `erase_step` connects it to these actual cached states. -/
theorem observe_evaluate_le {V : Type} [finV : Fintype V] [ordV : LinearOrder V]
    (width : Nat) (c : Channel) (order : EliminationOrder V)
    (fs : List (ObservedFactor V (Fin q) R)) (cached : CachedState fs)
    (bounded : ScopeBound width order (erase fs)) :
    c.observe (evaluate order fs).work ≤
      rowCap q width * pivotUnits c order fs + finalUnits c order fs := by
  induction order generalizing finV ordV with
  | done empty =>
      simp [evaluate, work_endpoint_cached empty fs cached, pivotUnits, finalUnits]
  | step v rest ih =>
      have hb := bounded.1
      have ht : ScopeBound width rest (erase (step v fs).value) := by
        rw [erase_step]
        exact bounded.2
      have htail := ih (step v fs).value (cachedState_step v fs cached) ht
      simp only [evaluate, Channel.observe_add, pivotUnits, finalUnits]
      rw [Channel.observe_step c v fs cached]
      calc
        _ ≤ rowCap q width * c.rowUnits (selected v fs) +
            (rowCap q width * pivotUnits c rest (step v fs).value +
              finalUnits c rest (step v fs).value) :=
          Nat.add_le_add (Nat.mul_le_mul_right _ (pow_le_rowCap hb)) htail
        _ = _ := by rw [Nat.mul_add, Nat.add_assoc]

/-- Stored input tables establish their own cached-reader invariant. The input
bag certificate therefore suffices for every channel of the actual evaluator. -/
theorem Decomposition.observe_evaluateStored_le {V : Type} [Fintype V] [LinearOrder V]
    {width : Nat} (d : Decomposition V width) (c : Channel)
    (fs : List (TabulatedFactor V (Fin q) R))
    (covered : Bagged d.bags (fs.map TabulatedFactor.toFactor)) :
    c.observe (evaluateStored d.order fs).work ≤
      rowCap q width * pivotUnits c d.order (prepareInputs fs).value +
        finalUnits c d.order (prepareInputs fs).value := by
  simp only [evaluateStored, Channel.observe_add, Channel.observe_prepareInputs, Nat.zero_add]
  apply observe_evaluate_le width c d.order _ (cachedState_prepareInputs fs)
  rw [erase_prepareInputs]
  exact d.scopeBound _ covered

/-- The number of per-row units in the row channel is the number of variables. -/
theorem pivotUnits_rows {V : Type} [finV : Fintype V] [ordV : LinearOrder V]
    (order : EliminationOrder V) (fs : List (ObservedFactor V (Fin q) R)) :
    pivotUnits .rows order fs = order.length := by
  induction order generalizing finV ordV with
  | done empty => rfl
  | step v rest ih => simp [pivotUnits, Channel.rowUnits, EliminationOrder.length, ih, Nat.add_comm]

@[simp] theorem finalUnits_rows {V : Type} [finV : Fintype V] [ordV : LinearOrder V]
    (order : EliminationOrder V) (fs : List (ObservedFactor V (Fin q) R)) :
    finalUnits .rows order fs = 0 := by
  induction order generalizing finV ordV with
  | done empty => rfl
  | step v rest ih => exact ih _

/-- At most one width-bounded table per variable is materialized by the executor.
Input tables are supplied data; their own original `q^arity` storage is separate. -/
theorem Decomposition.rows_le {V : Type} [Fintype V] [LinearOrder V]
    {width : Nat} (d : Decomposition V width)
    (fs : List (TabulatedFactor V (Fin q) R))
    (covered : Bagged d.bags (fs.map TabulatedFactor.toFactor)) :
    (evaluateStored d.order fs).work.arrayPushes ≤ rowCap q width * Fintype.card V := by
  simpa only [Channel.observe, pivotUnits_rows, finalUnits_rows, Nat.add_zero,
    EliminationOrder.length_eq_card] using d.observe_evaluateStored_le .rows fs covered

/-- Addition units are exactly one pivot-colour pass per variable. -/
theorem pivotUnits_additions {V : Type} [finV : Fintype V] [ordV : LinearOrder V]
    (order : EliminationOrder V) (fs : List (ObservedFactor V (Fin q) R)) :
    pivotUnits .additions order fs = q * order.length := by
  induction order generalizing finV ordV with
  | done empty => simp [pivotUnits, EliminationOrder.length]
  | step v rest ih =>
      simp [pivotUnits, Channel.rowUnits, EliminationOrder.length, ih, Nat.mul_add, Nat.add_comm]

@[simp] theorem finalUnits_additions {V : Type} [finV : Fintype V] [ordV : LinearOrder V]
    (order : EliminationOrder V) (fs : List (ObservedFactor V (Fin q) R)) :
    finalUnits .additions order fs = 0 := by
  induction order generalizing finV ordV with
  | done empty => rfl
  | step v rest ih => exact ih _

/-- Each generated row sums `q` colours using the actual observed coefficient
addition loop. Empty domains consequently perform no coefficient additions. -/
theorem Decomposition.additions_le {V : Type} [Fintype V] [LinearOrder V]
    {width : Nat} (d : Decomposition V width)
    (fs : List (TabulatedFactor V (Fin q) R))
    (covered : Bagged d.bags (fs.map TabulatedFactor.toFactor)) :
    (evaluateStored d.order fs).work.coefficientAdditions ≤
      rowCap q width * (q * Fintype.card V) := by
  simpa only [Channel.observe, pivotUnits_additions, finalUnits_additions, Nat.add_zero,
    EliminationOrder.length_eq_card] using d.observe_evaluateStored_le .additions fs covered

end Counting.Algorithm.VariableEliminationWidth
