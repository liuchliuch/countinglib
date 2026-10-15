import Mathlib.Data.List.FinRange

/-!
# Measured generation of finite ordinal ranges

`generateFinRange` builds the ascending list of `Fin n` directly, using a
remaining-length recursion and an incrementing natural-number cursor. It does
not call `List.finRange`, map an existing list, or perform a list traversal.
The equality with `List.finRange` is a correctness theorem about the result.

The counters charge list cons allocations, calls that inspect the remaining
length (including the final zero case), cursor increments, and existing-list
traversals. The unique nil result is recorded separately. Instrumentation
bookkeeping, erased proofs, and record construction are not charged by this
primitive-operation model; these counts are not a bit-time bound.
-/

namespace Counting.Algorithm.VariableEliminationLayout

/-- Primitive operation counts for the finite ordinal generator. -/
structure FinRangeCost where
  /-- Allocation sites for nonempty list cells. -/
  listCons : Nat
  /-- Inspections of the remaining length, including its final zero case. -/
  loopTests : Nat
  /-- Executed increments of the cursor used as the next `Fin.val`. -/
  natIncrements : Nat
  /-- Visits to cells of a previously constructed list. -/
  listTraversals : Nat
  /-- Executions of the branch returning the empty list. -/
  nilResults : Nat
  deriving DecidableEq, Repr

/-- The operations performed when the remaining length is zero. -/
def FinRangeCost.done : FinRangeCost := ⟨0, 1, 0, 0, 1⟩

/-- Add the operations of one nonzero recursion step. -/
def FinRangeCost.step (cost : FinRangeCost) : FinRangeCost :=
  ⟨cost.listCons + 1, cost.loopTests + 1, cost.natIncrements + 1,
    cost.listTraversals, cost.nilResults⟩

/-- Cons and nil construction sites, counting the final empty-list branch. -/
def FinRangeCost.listConstructions (cost : FinRangeCost) : Nat :=
  cost.listCons + cost.nilResults

/-- Sum of the five explicitly recorded primitive operation counts. -/
def FinRangeCost.total (cost : FinRangeCost) : Nat :=
  cost.listCons + cost.loopTests + cost.natIncrements +
    cost.listTraversals + cost.nilResults

/-- An executable generated list together with its primitive operation counts. -/
structure FinRangeResult (n : Nat) where
  values : List (Fin n)
  cost : FinRangeCost
  deriving Repr

/-- Build `remaining` ascending ordinals from `start`, with a bounded cursor.

The recursive call decreases `remaining` and increments `start`. Each nonzero
step allocates exactly one result-list cell, and the zero step returns nil.
-/
def generateFinRangeFrom (n : Nat) :
    (remaining start : Nat) → start + remaining ≤ n → FinRangeResult n
  | 0, _, _ => ⟨[], FinRangeCost.done⟩
  | remaining + 1, start, h =>
      let tail := generateFinRangeFrom n remaining (start + 1) (by omega)
      ⟨⟨start, by omega⟩ :: tail.values, tail.cost.step⟩

/-- Direct generation of all finite ordinals, including the empty range. -/
def generateFinRange (n : Nat) : FinRangeResult n :=
  generateFinRangeFrom n n 0 (by omega)

/-- The helper generates its specified ascending interval. -/
theorem generateFinRangeFrom_values (n remaining start : Nat)
    (h : start + remaining ≤ n) :
    (generateFinRangeFrom n remaining start h).values =
      List.ofFn (fun i : Fin remaining => (⟨start + i.val, by omega⟩ : Fin n)) := by
  induction remaining generalizing start with
  | zero => simp [generateFinRangeFrom]
  | succ remaining ih =>
      rw [generateFinRangeFrom, List.ofFn_succ]
      simp only [Fin.val_zero, Nat.add_zero]
      congr 1
      rw [ih]
      congr 1
      funext i
      apply Fin.ext
      simp [Nat.add_comm, Nat.add_left_comm]

/-- The executable generator has exactly the conventional finite-range order. -/
@[simp] theorem generateFinRange_values (n : Nat) :
    (generateFinRange n).values = List.finRange n := by
  rw [generateFinRange, generateFinRangeFrom_values]
  simp [List.finRange]

/-- All costs follow the actual recursive execution, independently of its cursor. -/
theorem generateFinRangeFrom_cost (n remaining start : Nat)
    (h : start + remaining ≤ n) :
    (generateFinRangeFrom n remaining start h).cost =
      ⟨remaining, remaining + 1, remaining, 0, 1⟩ := by
  induction remaining generalizing start with
  | zero => rfl
  | succ remaining ih =>
      simp [generateFinRangeFrom, ih, FinRangeCost.step]

/-- Exact primitive counts for the finite ordinal generator. -/
@[simp] theorem generateFinRange_cost (n : Nat) :
    (generateFinRange n).cost = ⟨n, n + 1, n, 0, 1⟩ :=
  generateFinRangeFrom_cost n n 0 (by omega)

@[simp] theorem generateFinRange_listCons (n : Nat) :
    (generateFinRange n).cost.listCons = n := by
  simp

@[simp] theorem generateFinRange_loopTests (n : Nat) :
    (generateFinRange n).cost.loopTests = n + 1 := by
  simp

@[simp] theorem generateFinRange_natIncrements (n : Nat) :
    (generateFinRange n).cost.natIncrements = n := by
  simp

@[simp] theorem generateFinRange_listTraversals (n : Nat) :
    (generateFinRange n).cost.listTraversals = 0 := by
  simp

@[simp] theorem generateFinRange_nilResults (n : Nat) :
    (generateFinRange n).cost.nilResults = 1 := by
  simp

@[simp] theorem generateFinRange_listConstructions (n : Nat) :
    (generateFinRange n).cost.listConstructions = n + 1 := by
  simp [FinRangeCost.listConstructions]

/-- Linear exact total in the declared primitive-operation model. -/
@[simp] theorem generateFinRange_total (n : Nat) :
    (generateFinRange n).cost.total = 3 * n + 2 := by
  simp [FinRangeCost.total]
  omega

theorem generateFinRange_total_le (n : Nat) :
    (generateFinRange n).cost.total ≤ 3 * (n + 1) := by
  rw [generateFinRange_total]
  omega

@[simp] theorem generateFinRange_length (n : Nat) :
    (generateFinRange n).values.length = n := by
  simp

theorem generateFinRange_nodup (n : Nat) :
    (generateFinRange n).values.Nodup := by
  simpa using List.nodup_finRange n

@[simp] theorem mem_generateFinRange (n : Nat) (i : Fin n) :
    i ∈ (generateFinRange n).values := by
  simp

end Counting.Algorithm.VariableEliminationLayout
