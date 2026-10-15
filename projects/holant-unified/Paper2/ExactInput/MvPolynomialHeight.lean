import Paper2.ExactInput.Bounds.RationalHeight
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.Linarith

/-! A fixed rational multivariate polynomial has an affine bit-height bound in
its arguments. This is a size theorem and assumes no arithmetic runtime oracle. -/
namespace Paper2.ExactInput
open Paper2.Algebraic

/-- Constants depend on the fixed polynomial, never on its input values. -/
theorem mvPolynomial_height_bound {σ : Type*} (p : MvPolynomial σ ℚ) :
    ∃ C : ℕ, ∀ (B : ℕ) (v : σ → ℚ), (∀ i, rationalBitHeight (v i) ≤ B) →
      rationalBitHeight (MvPolynomial.eval v p) ≤ C * (B + 1) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨rationalBitHeight a, fun B v _ => ?_⟩
    simp only [MvPolynomial.eval_C]
    nlinarith
  | add p q hp hq =>
    obtain ⟨C, hC⟩ := hp
    obtain ⟨D, hD⟩ := hq
    refine ⟨C + D + 2, fun B v hv => ?_⟩
    rw [map_add]
    have ha := rationalBitHeight_add (MvPolynomial.eval v p) (MvPolynomial.eval v q)
    have hb := hC B v hv
    have hc := hD B v hv
    nlinarith
  | mul_X p i hp =>
    obtain ⟨C, hC⟩ := hp
    refine ⟨C + 1, fun B v hv => ?_⟩
    simp only [map_mul, MvPolynomial.eval_X]
    have ha := rationalBitHeight_mul (MvPolynomial.eval v p) (v i)
    have hb := hC B v hv
    have hc := hv i
    nlinarith

/-- A single constant uniformly bounds any fixed finite list of rational
polynomials, including an empty list. -/
theorem mvPolynomial_family_height_bound {σ τ : Type*} [Fintype τ]
    (p : τ → MvPolynomial σ ℚ) :
    ∃ C : ℕ, ∀ (B : ℕ) (v : σ → ℚ), (∀ i, rationalBitHeight (v i) ≤ B) →
      ∀ t, rationalBitHeight (MvPolynomial.eval v (p t)) ≤ C * (B + 1) := by
  classical
  choose C hC using fun t => mvPolynomial_height_bound (p t)
  refine ⟨∑ t, C t, fun B v hv t => ?_⟩
  exact (hC t B v hv).trans (Nat.mul_le_mul_right _
    (Finset.single_le_sum (fun i _ => Nat.zero_le (C i)) (Finset.mem_univ t)))

end Paper2.ExactInput
