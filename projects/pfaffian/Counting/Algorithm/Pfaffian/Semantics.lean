import Counting.Algorithm.Pfaffian.Program
import PfaffianPort.PfaffianPivotSemantics

/-!
# Exact semantics of first-nonzero Pfaffian elimination

These adapters preserve the hypotheses of the fixed PlanarHom source at commit
`db68e745380769c38c8347736d2d84fcde38263c`, migrated under `PfaffianPort`.
The semantic target is the literal signed pairing sum. The executable evaluator
is the materialized first-nonzero elimination program.

Skew symmetry and zero diagonal are separate assumptions, including in
characteristic two. A supported evaluation also requires a strictly increasing
active list. These are semantic correctness results; bit-time and machine
refinement are separate interfaces.
-/

namespace Counting.Algorithm.Pfaffian

/-- The literal signed pairing sum supported on an active vertex set. -/
noncomputable abbrev supportedPfaffian {V R : Type*} [LinearOrder V] [Fintype V]
    [CommRing R] (S : Finset V) (A : Matrix V V R) : R :=
  PfaffianPort.MultiGraph.supportedPfaffian S A

/-- The literal signed pairing sum on every vertex of the matrix. -/
noncomputable abbrev pairingPfaffian {V R : Type*} [LinearOrder V] [Fintype V]
    [CommRing R] (A : Matrix V V R) : R :=
  PfaffianPort.MultiGraph.pairingPfaffian A

/-- Executable first-nonzero elimination with materialized matrix updates. -/
abbrev evaluate {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (active : List (Fin n)) : F :=
  PfaffianPort.MultiGraph.PfaffianElimination.evaluate A active

/-- On a strictly increasing active list, elimination agrees with the literal
supported pairing sum. No nonzero-pivot assumption is imposed on the input. -/
theorem evaluate_eq_supportedPfaffian {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (active : List (Fin n))
    (hskew : ∀ u v, A v u = -A u v) (hdiag : ∀ u, A u u = 0)
    (hordered : active.Pairwise (· < ·)) :
    evaluate A active = supportedPfaffian active.toFinset A :=
  PfaffianPort.MultiGraph.PfaffianElimination.evaluate_eq_supportedPfaffian
    A active hskew hdiag hordered

/-- On the full ordered vertex list, elimination equals the signed pairing
Pfaffian, for every dimension including zero and odd dimensions. -/
theorem evaluate_eq_pairingPfaffian {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (hskew : ∀ u v, A v u = -A u v) (hdiag : ∀ u, A u u = 0) :
    evaluate A (List.finRange n) = pairingPfaffian A :=
  PfaffianPort.MultiGraph.PfaffianElimination.evaluate_eq_pairingPfaffian A hskew hdiag

/-- The empty active list returns the empty product. -/
@[simp] theorem evaluate_nil {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) : evaluate A [] = 1 :=
  PfaffianPort.MultiGraph.PfaffianElimination.evaluate_nil A

/-- A row with no nonzero active partner takes the exact zero branch. -/
theorem evaluate_cons_noPivot {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (i : Fin n) (xs : List (Fin n))
    (hzero : ∀ j ∈ xs, A i j = 0) : evaluate A (i :: xs) = 0 :=
  PfaffianPort.MultiGraph.PfaffianElimination.evaluate_cons_noPivot A i xs hzero

/-- Odd dimensions have no pairings, hence an alternating matrix evaluates to zero. -/
theorem evaluate_eq_zero_of_odd {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (hn : Odd n)
    (hskew : ∀ u v, A v u = -A u v) (hdiag : ∀ u, A u u = 0) :
    evaluate A (List.finRange n) = 0 := by
  rw [evaluate_eq_pairingPfaffian A hskew hdiag]
  exact PfaffianPort.MultiGraph.pairingPfaffian_eq_zero_of_odd (by simpa using hn) A

end Counting.Algorithm.Pfaffian
