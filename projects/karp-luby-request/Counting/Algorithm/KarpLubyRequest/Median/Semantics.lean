import Counting.Algorithm.KarpLubyMachine.NumeratorMedian

/-!
# Occurrence-sensitive natural upper median

The finite implementation counts physical list occurrences on two unary stacks.
The semantic counters below specify those stack lengths; they are never control
registers. Their strict majority test is exactly the frozen R1 upper-median rule.
-/
namespace Counting.Algorithm.KarpLubyRequest.Median
open Counting.Algorithm.KarpLubyMachine

def below (xs : List ℕ) (a : ℕ) : ℕ := (xs.filter fun x => decide (x ≤ a)).length
def above (xs : List ℕ) (a : ℕ) : ℕ := (xs.filter fun x => decide (a < x)).length
def eligible (xs : List ℕ) (a : ℕ) : Bool := decide (above xs a < below xs a)

@[simp] theorem below_nil (a : ℕ) : below [] a = 0 := rfl
@[simp] theorem above_nil (a : ℕ) : above [] a = 0 := rfl
@[simp] theorem below_cons (x : ℕ) (xs : List ℕ) (a : ℕ) :
    below (x :: xs) a = below xs a + if x ≤ a then 1 else 0 := by
  by_cases h : x ≤ a <;> simp [below, h, Nat.add_comm]
@[simp] theorem above_cons (x : ℕ) (xs : List ℕ) (a : ℕ) :
    above (x :: xs) a = above xs a + if a < x then 1 else 0 := by
  by_cases h : a < x <;> simp [above, h, Nat.add_comm]

theorem count_partition (xs : List ℕ) (a : ℕ) : below xs a + above xs a = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [below_cons, above_cons, List.length_cons]
    by_cases h : x ≤ a
    · have hn : ¬ a < x := by omega
      rw [if_pos h, if_neg hn]
      omega
    · have hn : a < x := by omega
      rw [if_neg h, if_pos hn]
      omega

theorem eligible_half (xs : List ℕ) (a : ℕ) :
    eligible xs a = decide (xs.length / 2 < below xs a) := by
  have h := count_partition xs a
  unfold eligible
  by_cases hm : above xs a < below xs a
  · have hh : xs.length / 2 < below xs a := by omega
    simp only [hm, hh, decide_true]
  · have hh : ¬ xs.length / 2 < below xs a := by omega
    simp only [hm, hh, decide_false]

theorem below_ofFn (g : ℕ) (z : Fin g → ℕ) (a : ℕ) :
    below (List.ofFn z) a = (NumeratorMedian.countBelow g z a).value := by
  induction g with
  | zero => rfl
  | succ g ih =>
    rw [List.ofFn_succ, below_cons, ih]
    dsimp only [NumeratorMedian.countBelow]
    by_cases h : z 0 ≤ a <;> simp only [h, ite_true, ite_false, Nat.add_zero]

theorem eligible_ofFn (g : ℕ) (z : Fin g → ℕ) (a : ℕ) :
    eligible (List.ofFn z) a = (NumeratorMedian.eligible g z a).value := by
  rw [eligible_half, List.length_ofFn, below_ofFn]
  rfl

/-- Combining two optional minima does not invent a sentinel observation. -/
def merge : Option ℕ → Option ℕ → Option ℕ
  | none, q => q
  | q, none => q
  | some a, some b => some (min a b)

@[simp] theorem merge_none (q : Option ℕ) : merge q none = q := by cases q <;> rfl
@[simp] theorem none_merge (q : Option ℕ) : merge none q = q := rfl
theorem merge_assoc (p q r : Option ℕ) : merge (merge p q) r = merge p (merge q r) := by
  cases p <;> cases q <;> cases r <;> simp [merge, min_assoc]
theorem merge_comm (p q : Option ℕ) : merge p q = merge q p := by
  cases p <;> cases q <;> simp [merge, min_comm]

/-- One left-to-right update, using the same strict comparison as the machine. -/
def insert (q : Option ℕ) (a : ℕ) : Option ℕ :=
  match q with
  | none => some a
  | some b => if a < b then some a else some b

theorem insert_eq_merge (q : Option ℕ) (a : ℕ) : insert q a = merge q (some a) := by
  cases q with
  | none => rfl
  | some b =>
    by_cases h : a < b
    · simp [insert, merge, h, min_eq_right (Nat.le_of_lt h)]
    · simp [insert, merge, h, min_eq_left (Nat.le_of_not_gt h)]

def select (p : ℕ → Bool) : List ℕ → Option ℕ → Option ℕ
  | [], q => q
  | a :: as, q => select p as (if p a then insert q a else q)

theorem select_eq_merge (p : ℕ → Bool) (xs : List ℕ) (q : Option ℕ) :
    select p xs q = merge q (xs.filter p).min? := by
  induction xs generalizing q with
  | nil => simp [select]
  | cons a as ih =>
    cases hp : p a
    · simp [select, hp, ih]
    · rw [select, hp]
      simp only [Bool.true_eq, ↓reduceIte, ih, insert_eq_merge, merge_assoc]
      simp only [List.filter_cons, hp, Bool.true_eq, ↓reduceIte]
      cases hq : (as.filter p).min? <;> simp [merge, hq]

def value (xs : List ℕ) : ℕ := (select (eligible xs) xs none).getD 0

/-- Exact bridge to the previously accepted natural selector, including g = 0. -/
theorem value_ofFn (g : ℕ) (z : Fin g → ℕ) :
    value (List.ofFn z) = (NumeratorMedian.median g z).value := by
  unfold value
  rw [select_eq_merge, none_merge]
  have hp : eligible (List.ofFn z) = fun a => (NumeratorMedian.eligible g z a).value := by
    funext a; exact eligible_ofFn g z a
  rw [hp]
  change _ = (NumeratorMedian.select (NumeratorMedian.eligible g z)
    (NumeratorMedian.collect g z).value).value.getD 0
  rw [NumeratorMedian.collect_value, NumeratorMedian.select_value]

@[simp] theorem value_nil : value [] = 0 := rfl

end Counting.Algorithm.KarpLubyRequest.Median
