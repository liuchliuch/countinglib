import Holant.Proofs.Tractability.AffineMachine.Elimination

/-!
# Boolean affine input and elimination semantics

The support is over `ZMod 2`; the phase is modulo four and its strictly
upper-triangular mixed coefficients are zero or two. The scale may be zero.
This is a Boolean quadratic-sum API, not a quadratic-sum algorithm over arbitrary
fields. The source provider remains unique; these abbreviations do not create a
second representation of the upstream structures.
-/
namespace Counting.Algorithm.Affine

open Holant Holant.Tractable
open Holant.LocalDrafts.Tractability

abbrev Support := AffineSystem
abbrev Phase := QuadraticPhase
abbrev Input := AffineMachine.State

noncomputable abbrev value {n : ℕ} (A : Input n) := A.value
noncomputable abbrev partition {n : ℕ} (A : Input n) := A.partition
noncomputable abbrev evaluate {n : ℕ} (A : Input n) := AffineMachine.evaluate A
noncomputable abbrev rounds {n : ℕ} (A : Input n) := AffineMachine.rounds A

/-- The recursive algorithm eliminates one variable on each active branch. -/
theorem evaluate_correct {n : ℕ} (A : Input n) : evaluate A = partition A :=
  AffineMachine.evaluate_eq_partition A

/-- This counts eliminations, not arithmetic operations or bit transitions. -/
theorem rounds_le {n : ℕ} (A : Input n) : rounds A ≤ n := AffineMachine.rounds_le A

theorem inconsistent {n : ℕ} (A : Input n)
    (h : AffineMachine.Constraint.badRow A.support = true) : evaluate A = 0 := by
  rw [evaluate_correct]
  exact AffineMachine.Constraint.partition_badRow A h

/-- A genuine Boolean support pivot; no division by a complex coefficient. -/
theorem pivot_correct {n : ℕ} (A : Input (n + 1))
    (r : Fin A.support.rows) (j : Fin (n + 1))
    (h : AffineMachine.Constraint.pivot A.support = some (r, j)) :
    evaluate (AffineMachine.Constraint.eliminate A r j) = partition A := by
  rw [evaluate_correct]
  exact (AffineMachine.Constraint.partition_eliminate A r j
    (AffineMachine.Constraint.pivot_some _ r j h)).symm

/-- The four phase branches retain their parity constraint and multiplier. -/
theorem free_correct {n : ℕ} (A : Input (n + 1))
    (hp : AffineMachine.Constraint.pivot A.support = none)
    (hb : AffineMachine.Constraint.badRow A.support = false) :
    evaluate (AffineMachine.FreePhase.eliminate A) = partition A := by
  rw [evaluate_correct]
  exact (AffineMachine.FreePhase.partition_eliminate A hp hb).symm

end Counting.Algorithm.Affine
