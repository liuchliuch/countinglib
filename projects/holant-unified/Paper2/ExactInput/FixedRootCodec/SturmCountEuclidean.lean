import Paper2.ExactInput.FixedRootCodec.SturmCount

/-! A genuine negative Euclidean remainder sequence ending in a nonzero
constant satisfies all local algebraic Sturm conditions. This adapter keeps
the generated quotients and actual polynomial equations explicit. -/
namespace Paper2.ExactInput.FixedRootCodec.SturmCount
open Polynomial
noncomputable section

structure NegativeRemainderChain where
  tailLength : ℕ
  polynomial : ℕ → ℝ[X]
  quotient : ℕ → ℝ[X]
  head_ne : polynomial 0 ≠ 0
  derivative : polynomial 1 = (polynomial 0).derivative
  terminal : ℝ
  terminal_ne : terminal ≠ 0
  last : polynomial (tailLength+1) = C terminal
  recurrence : ∀ i < tailLength,
    polynomial i = quotient i*polynomial (i+1)-polynomial (i+2)

namespace NegativeRemainderChain

theorem last_eval_ne (S : NegativeRemainderChain) (x : ℝ) :
    (S.polynomial (S.tailLength+1)).eval x ≠ 0 := by
  simpa [S.last] using S.terminal_ne

/-- A pair of consecutive zeros propagates to the terminal constant, which
rules out such a pair at every evaluation point. -/
theorem adjacent_eval_ne (S : NegativeRemainderChain) (i : ℕ)
    (hi : i < S.tailLength+1) (x : ℝ) (hz : (S.polynomial i).eval x = 0) :
    (S.polynomial (i+1)).eval x ≠ 0 := by
  have hno : ∀ k i, i+k=S.tailLength → (S.polynomial i).eval x=0 →
      (S.polynomial (i+1)).eval x=0 → False := by
    intro k
    induction k with
    | zero =>
      intro j hj h0 h1
      have hj' : j=S.tailLength := by omega
      subst j
      exact S.last_eval_ne x h1
    | succ k ih =>
      intro j hj h0 h1
      have hjlt : j < S.tailLength := by omega
      have hr := congrArg (fun p : ℝ[X] => p.eval x) (S.recurrence j hjlt)
      have h2 : (S.polynomial (j+2)).eval x=0 := by
        simp only [eval_sub, eval_mul, h0, h1, mul_zero, zero_sub] at hr
        exact neg_eq_zero.mp hr.symm
      exact ih (j+1) (by omega) h1 (by simpa [Nat.add_assoc] using h2)
  intro hn
  exact hno (S.tailLength-i) i (by omega) hz hn

def toChain (S : NegativeRemainderChain) : Chain where
  tailLength := S.tailLength
  polynomial := S.polynomial
  head_ne := S.head_ne
  derivative := S.derivative
  last_ne := S.last_eval_ne
  adjacent := S.adjacent_eval_ne
  opposite := by
    intro i hi x hz
    have hr := congrArg (fun p : ℝ[X] => p.eval x) (S.recurrence i hi)
    simp only [eval_sub, eval_mul, hz, mul_zero, zero_sub] at hr
    linear_combination hr

/-- Exact distinct-real-root count from the actual polynomial remainder
identities; no separately supplied Sturm or counting certificate is needed. -/
theorem count_Ioc (S : NegativeRemainderChain) (a b : ℝ) (hab : a ≤ b) :
    S.toChain.doubledVariation a-S.toChain.doubledVariation b =
      2*((S.toChain.roots.filter fun r => a < r ∧ r ≤ b).card : ℤ) :=
  S.toChain.count_Ioc a b hab

end NegativeRemainderChain
end
end Paper2.ExactInput.FixedRootCodec.SturmCount

