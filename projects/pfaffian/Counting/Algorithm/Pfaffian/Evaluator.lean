import Counting.Algorithm.Pfaffian.Semantics
import PfaffianPort.OccurrencePfaffianEvaluationMachines

/-!
# Runtime-dimensional exact Pfaffian evaluation

The executable input is a nested list. Its outer length determines the matrix
order. Normalization reads the upper triangle, fills absent entries with zero,
negates into the lower triangle, and zeroes the diagonal. On an alternating
square matrix this preserves every entry.

The runtime theorems below retain the fixed finite-dimensional rational basis
and the exact codecs of the source at commit
`db68e745380769c38c8347736d2d84fcde38263c`. They use upstream `FP`, whose witness
contains an actual TM2 program and a polynomial bound on encoded bit time.
No equivalence with the separate F1 machine wrapper is asserted here.
-/

namespace Counting.Algorithm.Pfaffian

/-- Runtime-dimensional, potentially ragged input rows. -/
abbrev Grid (K : Type) := PfaffianPort.PfaffianList.Grid K

/-- Row-major materialization of all entries of a square matrix. -/
abbrev matrixRows {K : Type} {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Grid K :=
  PfaffianPort.PfaffianList.matrixRows A

/-- Total alternating normalization determined by the upper triangle. -/
abbrev normalizeGrid {K : Type} [Field K] (g : Grid K) : Grid K :=
  PfaffianPort.PfaffianList.normalizeGrid g

/-- Executable first-nonzero elimination on the normalized input rows. -/
abbrev evaluateGrid {K : Type} [Field K] [DecidableEq K] (g : Grid K) : K :=
  PfaffianPort.PfaffianList.evaluateGrid g

/-- The exact nested-list codec for a fixed rational basis of the coefficient field. -/
noncomputable abbrev gridEncoding {K : Type} [Field K] [Algebra ℚ K]
    {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K) :
    PfaffianPort.Complexity.BitEncoding (Grid K) :=
  PfaffianPort.PfaffianList.gridEncoding basis

/-- The total row evaluator refines the materialized matrix program on every
alternating square input, with matrix order varying independently of the field. -/
theorem evaluateGrid_eq_elimination {K : Type} [Field K] [Algebra ℚ K]
    [DecidableEq K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (hskew : ∀ i j, A j i = -A i j) (hdiag : ∀ i, A i i = 0) :
    evaluateGrid (matrixRows A) = evaluate A (List.finRange n) :=
  PfaffianPort.PfaffianList.evaluateGrid_eq_elimination A hskew hdiag

/-- Signed-pairing correctness over a rational algebra with decidable equality,
without a finite-dimensional basis premise. The algebra premise is retained from
the source list-program bridge; the separate matrix semantic API works over any field. -/
theorem evaluateGrid_eq_pairingPfaffian {K : Type} [Field K] [Algebra ℚ K]
    [DecidableEq K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (hskew : ∀ i j, A j i = -A i j) (hdiag : ∀ i, A i i = 0) :
    evaluateGrid (matrixRows A) = pairingPfaffian A :=
  (evaluateGrid_eq_elimination A hskew hdiag).trans
    (evaluate_eq_pairingPfaffian A hskew hdiag)

variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}

/-- Upstream FP under the actual input/output bit encodings. The field and its
basis are fixed; the nested-list matrix order is part of the input. -/
theorem fp_evaluateGrid (basis : Module.Basis (Fin dimension) ℚ K) :
    PfaffianPort.Complexity.FP (gridEncoding basis)
      (PfaffianPort.Complexity.numberFieldEncoding basis) (evaluateGrid (K := K)) :=
  PfaffianPort.PfaffianList.fp_evaluateGrid basis

/-- The executable rows evaluate to the literal signed pairing sum. This
basis-indexed adapter preserves the signature of the upstream endpoint. -/
theorem evaluateGrid_matrixRows (basis : Module.Basis (Fin dimension) ℚ K)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hskew : ∀ i j, A j i = -A i j) (hdiag : ∀ i, A i i = 0) :
    evaluateGrid (matrixRows A) = pairingPfaffian A :=
  PfaffianPort.PfaffianList.evaluateGrid_matrixRows basis A hskew hdiag

/-- Exact executable evaluation, upstream encoded polynomial bit time, and
signed-pairing correctness in one endpoint. No nonsingularity or parity promise
is needed; the empty and odd-dimensional cases are included. -/
theorem certified_evaluateGrid (basis : Module.Basis (Fin dimension) ℚ K) :
    PfaffianPort.Complexity.FP (gridEncoding basis)
      (PfaffianPort.Complexity.numberFieldEncoding basis) (evaluateGrid (K := K)) ∧
    ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
      (∀ i j, A j i = -A i j) → (∀ i, A i i = 0) →
      evaluateGrid (matrixRows A) = pairingPfaffian A :=
  PfaffianPort.PfaffianList.certified_evaluateGrid basis

end Counting.Algorithm.Pfaffian
