/-
Extracted from Holant/Complexity/BinaryInterpolation/LagrangeValues.lean
in https://github.com/liuchliuch/holant-dichotomy-lean,
commit 97731bce1618bef0d9ee7911b6ac8bc8698077b2.
Source Git blob: 4e5da143ada48cce1494fe5dfbb61297cd01b2f4.

The upstream repository's LICENSE at this commit is Apache License 2.0.
License source: https://github.com/liuchliuch/holant-dichotomy-lean/blob/97731bce1618bef0d9ee7911b6ac8bc8698077b2/LICENSE
See provenance/core-source.json for checked source hashes and declaration mapping.

Changes: selected the four field-polynomial declarations, changed their namespace,
removed the unused network and geometric-node dependencies, and added documentation.
The definitions, theorem statements, and proof arguments are preserved.
-/
import Mathlib.LinearAlgebra.Lagrange

/-!
# Exact recovery of a polynomial's degree-bound coefficient

The explicit Lagrange formula recovers the coefficient at a degree bound `m`
from values at `m + 1` distinct field elements. This is an algebraic correctness
result; an effective field representation, an executable implementation, and a
bit-cost bound are separate obligations.
-/

namespace Counting.Algorithm.Interpolation

open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K] {m : ℕ}

/-- The product of the differences from one interpolation node to all the others. -/
def interpolationDenominator (nodes : Fin (m + 1) → K) (i : Fin (m + 1)) : K :=
  ∏ j ∈ Finset.univ.erase i, (nodes i - nodes j)

/-- The explicit Lagrange sum for the coefficient at the degree bound `m`. -/
def recoverTop (nodes values : Fin (m + 1) → K) : K :=
  ∑ i, values i / interpolationDenominator nodes i

/-- Pairwise distinct interpolation nodes give nonzero denominators. -/
theorem interpolationDenominator_ne_zero (nodes : Fin (m + 1) → K)
    (hi : Function.Injective nodes) (i : Fin (m + 1)) :
    interpolationDenominator nodes i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro he
  exact (Finset.mem_erase.mp hj).1 (hi he).symm

/-- For degree at most `m`, `m + 1` distinct evaluations recover the coefficient of
`X ^ m`, including the case where the actual degree is smaller than `m`. -/
theorem recoverTop_eq_coefficient (nodes : Fin (m + 1) → K)
    (hi : Function.Injective nodes) (P : Polynomial K) (hP : P.natDegree ≤ m) :
    recoverTop nodes (fun i => P.eval (nodes i)) = P.coeff m := by
  have hd : P.degree < ((Finset.univ : Finset (Fin (m + 1))).card : ℕ) := by
    simp only [Finset.card_univ, Fintype.card_fin]
    calc
      P.degree ≤ (P.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ ≤ (m : WithBot ℕ) := by exact_mod_cast hP
      _ < ((m + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self m
  have h := Lagrange.coeff_eq_sum (s := Finset.univ) (v := nodes) hi.injOn hd
  simpa [recoverTop, interpolationDenominator] using h.symm

end

end Counting.Algorithm.Interpolation
