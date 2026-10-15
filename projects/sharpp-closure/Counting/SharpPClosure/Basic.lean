import Counting.Foundation.Witness

/-!
# Exact prefix witnesses with one false suffix

This layer has no machine imports. Short witnesses are rejected explicitly.
For every sufficiently long fixed source length, the suffix has exactly one
acceptable filling, including zero-length prefixes and zero-length padding.
-/

namespace Counting.SharpPClosure

open Counting.Foundation

/-- Total verifier semantics: require the requested prefix to exist, use exactly
that prefix, and reject every true bit in the remaining suffix. -/
def paddedAccept (length : ℕ) (accept : List Bool → Bool) (w : List Bool) : Bool :=
  decide (length ≤ w.length) && accept (w.take length) && !(w.drop length).any id

@[simp] theorem paddedAccept_short (n : ℕ) (accept : List Bool → Bool)
    (w : List Bool) (h : w.length < n) : paddedAccept n accept w = false := by
  simp [paddedAccept, Nat.not_le_of_lt h]

/-- An empty prefix still requires the entire witness to be the unique false
filler; the target verifier is invoked on the empty word. -/
@[simp] theorem paddedAccept_zero (accept : List Bool → Bool) (w : List Bool) :
    paddedAccept 0 accept w = (accept [] && !w.any id) := by
  simp [paddedAccept]

@[simp] theorem paddedAccept_empty (n : ℕ) (accept : List Bool → Bool) :
    paddedAccept n accept [] = (decide (n = 0) && accept []) := by
  simp [paddedAccept]

theorem noTrue_eq_replicate (xs : List Bool) :
    (!xs.any id) = decide (xs = List.replicate xs.length false) := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [List.replicate_succ, ih]

/-- Every exact prefix extends in precisely one permitted way. -/
theorem paddedAccept_append_false (n k : ℕ) (accept : List Bool → Bool)
    (w : List Bool) (h : w.length = n) :
    paddedAccept n accept (w ++ List.replicate k false) = accept w := by
  simp [paddedAccept, ← h]

/-- A nonzero suffix is rejected even when the prefix is accepted. -/
theorem paddedAccept_append_true (n : ℕ) (accept : List Bool → Bool)
    (w rest : List Bool) (h : w.length = n) :
    paddedAccept n accept (w ++ true :: rest) = false := by
  simp [paddedAccept, ← h]

/-- Reuse the foundational unique-padding bijection after proving that the
total verifier agrees on every word of the counted length. -/
theorem witnessCount_paddedAccept (n N : ℕ) (h : n ≤ N)
    (accept : List Bool → Bool) :
    witnessCount N (paddedAccept n accept) = witnessCount n accept := by
  have hN : n + (N - n) = N := Nat.add_sub_of_le h
  rw [← hN]
  calc
    witnessCount (n + (N - n)) (paddedAccept n accept) =
        witnessCount (n + (N - n)) (falsePadding n (N - n) accept) := by
      unfold witnessCount
      apply countAccepted_congr
      intro w
      simp [paddedAccept, falsePadding, noTrue_eq_replicate]
    _ = witnessCount n accept := witnessCount_falsePadding n (N - n) accept

/-- If the suffix test is omitted, precisely the forbidden factor appears. -/
theorem ignoredSuffix_inflation (n N : ℕ) (h : n ≤ N)
    (accept : List Bool → Bool) :
    witnessCount N (fun w => accept (w.take n)) =
      witnessCount n accept * 2 ^ (N - n) := by
  conv_lhs => rw [← Nat.add_sub_of_le h]
  exact witnessCount_ignored_padding n (N - n) accept

end Counting.SharpPClosure
