import Counting.Algorithm.KarpLubyRequest.Iteration.Run

/-!
# Conditional bounds for the real repeat compiler

Uniform body-time and intermediate-word bounds imply a bound linear in the
numeric repetition count, with the charged binary decrement overhead. A caller
must supply its actual body and intermediate-state bounds. In particular this
module does not turn an unbounded binary counter into a polynomial clock.
-/
namespace Counting.Algorithm.KarpLubyRequest.Iteration
open Turing Computability Holant.Complexity StackProtocol BinaryCompose IntegerArithmetic GraphPreprocessing

variable {α : Type}

theorem counterCharges_le (n : ℕ) : counterCharges n ≤ n * (2 * (encodeNat n).length + 3) := by
  unfold counterCharges
  calc
    _ ≤ ∑ k ∈ Finset.range n, (2 * (encodeNat n).length + 3) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k + 1 ≤ n := by have := Finset.mem_range.mp hk; omega
      have hb := borrowCount_le (encodeNat (k + 1))
      have hl : (encodeNat (k + 1)).length ≤ (encodeNat n).length := by
        rw [Holant.Algebraic.encodeNat_length, Holant.Algebraic.encodeNat_length]
        exact Nat.size_le_size hk'
      omega
    _ = _ := by simp

theorem bodyCharges_le (e : Encoding α Bool) (f : α → α) (sourceTime : α → ℕ)
    (n : ℕ) (x : α) (bodyBound wordBound : ℕ)
    (ht : ∀ i < n, sourceTime (f^[i] x) ≤ bodyBound)
    (hw : ∀ i < n, (e.encode (f^[i + 1] x)).length ≤ wordBound) :
    bodyCharges e f sourceTime n x ≤ n * (bodyBound + 2 * (wordBound + 1)) := by
  unfold bodyCharges
  calc
    _ ≤ ∑ i ∈ Finset.range n, (bodyBound + 2 * (wordBound + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have ht' := ht i hi'
      have hw' := hw i hi'
      omega
    _ = _ := by simp

theorem ticks_le (e : Encoding α Bool) (f : α → α) (sourceTime : α → ℕ)
    (n : ℕ) (x : α) (bodyBound wordBound : ℕ)
    (ht : ∀ i < n, sourceTime (f^[i] x) ≤ bodyBound)
    (hw : ∀ i < n, (e.encode (f^[i + 1] x)).length ≤ wordBound) :
    ticks e f sourceTime n x ≤
      1 + n * (bodyBound + 2 * (wordBound + 1) + 2 * (encodeNat n).length + 3) := by
  rw [ticks_eq_sum]
  have hb := bodyCharges_le e f sourceTime n x bodyBound wordBound ht hw
  have hc := counterCharges_le n
  nlinarith

/-- Coupling the actual source/run certificate with caller-supplied growth
bounds yields a measured execution theorem for this same compiled program. -/
theorem bounded_bit_cost (body : Machine) (e : Encoding α Bool) (f : α → α) (sourceTime : α → ℕ)
    (hbody : ∀ x, SourceRun body (e.encode x) (e.encode (f x)) (sourceTime x))
    (n : ℕ) (x : α) (bodyBound wordBound : ℕ)
    (ht : ∀ i < n, sourceTime (f^[i] x) ≤ bodyBound)
    (hw : ∀ i < n, (e.encode (f^[i + 1] x)).length ≤ wordBound) :
    (Primitive.run (program body) (ticks e f sourceTime n x)
      (some (cfg (own body 0) body.initial (ready body (encodeNat n) (e.encode x))))).1 ≤
        (8 + body.primitiveBudget) *
          (1 + n * (bodyBound + 2 * (wordBound + 1) + 2 * (encodeNat n).length + 3)) := by
  have hc := (bit_cost body e f sourceTime hbody n x).2
  rw [← ticks_eq_sum] at hc
  exact hc.trans (Nat.mul_le_mul_left _ (ticks_le e f sourceTime n x bodyBound wordBound ht hw))

end Counting.Algorithm.KarpLubyRequest.Iteration
