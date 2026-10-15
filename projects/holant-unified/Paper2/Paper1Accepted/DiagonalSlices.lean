import Paper2.Tractable.Scalars
import Paper2.Signature
import Mathlib.Tactic

/-! Exact mathematical boundary for Paper 1, arXiv:2609.00219v1,
Lemma 7.8 (Diagonal-slice integration), printed pp.128--129 / PDF pp.127--128.
The accepted statement is over complex coefficients. Algebraic descent is a
separate proved adapter; no Paper 2 contraction or classification is assumed.

`UnaryOnDiagonal` writes a simple tensor on t_i=t_j using the original port
labels. One of the two repeated labels may carry the constant unary 1, so this
is just the source's common-bit plus r-2-bit unary product, with its scalar.
-/
namespace Paper2
namespace DiagonalSlices
open scoped BigOperators

noncomputable def singleWord {r : ℕ} (i : Fin r) : Fin r → Bool := fun k => decide (k = i)
noncomputable def doubleWord {r : ℕ} (i j : Fin r) : Fin r → Bool :=
  fun k => decide (k = i ∨ k = j)

def UnaryOnDiagonal {K : Type*} [CommMonoidWithZero K] {r : ℕ}
    (h : Signature K r) (i j : Fin r) : Prop :=
  ∃ (c : K) (u : Fin r → Bool → K), c ≠ 0 ∧ (∀ k b, u k b ≠ 0) ∧
    ∀ t, t i = t j → h t = c * ∏ k, u k (t k)

def UnaryDiagonals {K : Type*} [CommMonoidWithZero K] {r : ℕ}
    (h : Signature K r) : Prop := ∀ i j, i ≠ j → UnaryOnDiagonal h i j

end DiagonalSlices

/-- Only the two conclusions literally asserted by official Paper 1 Lemma 7.8.
In particular the three-variable exceptional parameter is not assumed to be 1. -/
structure Paper1DiagonalSlicesAccepted where
  diagonal_large_7_8 : ∀ (r : ℕ), 4 ≤ r → ∀ h : Signature ℂ r,
    (∀ t, h t ≠ 0) → h (fun _ => false) = 1 → DiagonalSlices.UnaryDiagonals h →
    ∃ ρ : Fin r → ℂ, (∀ i, ρ i ≠ 0) ∧ ∀ t, h t = ∏ i, (if t i then ρ i else 1)
  diagonal_three_7_8 : ∀ h : Signature ℂ 3,
    (∀ t, h t ≠ 0) → h (fun _ => false) = 1 → DiagonalSlices.UnaryDiagonals h →
    ∃ (ρ : Fin 3 → ℂ) (κ : ℂ), (∀ i, ρ i ≠ 0) ∧ κ ≠ 0 ∧
      (∀ i, h (DiagonalSlices.singleWord i) = ρ i) ∧
      (∀ i j, i ≠ j → h (DiagonalSlices.doubleWord i j) = κ * ρ i * ρ j) ∧
      h (fun _ => true) = κ * ∏ i, ρ i

end Paper2
