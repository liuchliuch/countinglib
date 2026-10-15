import Counting.Algorithm.VariableElimination.Enumeration
import Mathlib.Data.List.Sort

/-!
# Counted preparation of canonical finite lists

The input is an explicit enumeration list. Insertion sort counts each list case,
order comparison, and allocated list cons cell at the operation that executes it.
The counters do not count their own bookkeeping or any bit-level implementation.
-/

namespace Counting.Algorithm.VariableEliminationLayout

universe u

/-- Logical data operations performed by preparation, separate from coefficient
or address arithmetic and from the instrumentation's own counters. -/
structure SortWork where
  listCases : Nat
  orderComparisons : Nat
  listCons : Nat
  deriving Repr, DecidableEq

structure SortedResult (α : Type u) where
  values : List α
  work : SortWork
  deriving Repr

/-- Insert one value, sharing the untouched suffix. Each failed comparison
reconstructs precisely one preceding cons cell. -/
def insertCounted {α : Type u} [LinearOrder α] (a : α) : List α → SortedResult α
  | [] => ⟨[a], ⟨1, 0, 1⟩⟩
  | b :: bs =>
      if a ≤ b then ⟨a :: b :: bs, ⟨1, 1, 2⟩⟩
      else
        let t := insertCounted a bs
        ⟨b :: t.values, ⟨t.work.listCases + 1, t.work.orderComparisons + 1,
          t.work.listCons + 1⟩⟩

/-- Actual recursive sorting and accumulation of its primitive operation counts. -/
def sortCounted {α : Type u} [LinearOrder α] : List α → SortedResult α
  | [] => ⟨[], ⟨1, 0, 0⟩⟩
  | a :: xs =>
      let tail := sortCounted xs
      let row := insertCounted a tail.values
      ⟨row.values, ⟨1 + tail.work.listCases + row.work.listCases,
        tail.work.orderComparisons + row.work.orderComparisons,
        tail.work.listCons + row.work.listCons⟩⟩

@[simp] theorem values_insertCounted {α : Type u} [LinearOrder α]
    (a : α) (xs : List α) :
    (insertCounted a xs).values = xs.orderedInsert (· ≤ ·) a := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      by_cases h : a ≤ b <;> simp [insertCounted, List.orderedInsert_cons, ih, h]

@[simp] theorem values_sortCounted {α : Type u} [LinearOrder α] (xs : List α) :
    (sortCounted xs).values = xs.insertionSort (· ≤ ·) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [sortCounted, ih]

@[simp] theorem length_values_sortCounted {α : Type u} [LinearOrder α] (xs : List α) :
    (sortCounted xs).values.length = xs.length := by simp [List.length_insertionSort]

/-- Number of comparisons in the worst-case insertion-sort recurrence. -/
def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + n

theorem comparisons_insertCounted_le {α : Type u} [LinearOrder α]
    (a : α) (xs : List α) : (insertCounted a xs).work.orderComparisons ≤ xs.length := by
  induction xs with
  | nil => simp [insertCounted]
  | cons b bs ih =>
      simp only [insertCounted, List.length_cons]
      split <;> simp_all only <;> omega

theorem cases_insertCounted_le {α : Type u} [LinearOrder α]
    (a : α) (xs : List α) : (insertCounted a xs).work.listCases ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [insertCounted]
  | cons b bs ih =>
      simp only [insertCounted, List.length_cons]
      split <;> simp_all only <;> omega

theorem cons_insertCounted_le {α : Type u} [LinearOrder α]
    (a : α) (xs : List α) : (insertCounted a xs).work.listCons ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [insertCounted]
  | cons b bs ih =>
      simp only [insertCounted, List.length_cons]
      split <;> simp_all only <;> omega

theorem comparisons_sortCounted_le {α : Type u} [LinearOrder α] (xs : List α) :
    (sortCounted xs).work.orderComparisons ≤ triangle xs.length := by
  induction xs with
  | nil => simp [sortCounted, triangle]
  | cons a xs ih =>
      have hi := comparisons_insertCounted_le a (sortCounted xs).values
      simp only [length_values_sortCounted] at hi
      simp only [sortCounted, List.length_cons, triangle]
      omega

theorem cons_sortCounted_le {α : Type u} [LinearOrder α] (xs : List α) :
    (sortCounted xs).work.listCons ≤ triangle (xs.length + 1) := by
  induction xs with
  | nil => simp [sortCounted, triangle]
  | cons a xs ih =>
      have hi := cons_insertCounted_le a (sortCounted xs).values
      simp only [length_values_sortCounted] at hi
      simp only [sortCounted, List.length_cons, triangle]
      simp only [triangle] at ih
      omega

theorem cases_sortCounted_le {α : Type u} [LinearOrder α] (xs : List α) :
    (sortCounted xs).work.listCases ≤ triangle (xs.length + 1) + xs.length + 1 := by
  induction xs with
  | nil => simp [sortCounted, triangle]
  | cons a xs ih =>
      have hi := cases_insertCounted_le a (sortCounted xs).values
      simp only [length_values_sortCounted] at hi
      simp only [sortCounted, List.length_cons, triangle]
      simp only [triangle] at ih
      omega

/-- Input representation: one occurrence of each element, in any order. No
sortedness or claimed output equality is assumed. -/
structure EnumerationSource (α : Type u) where
  values : List α
  nodup : values.Nodup
  complete : ∀ a, a ∈ values

namespace EnumerationSource

variable {α : Type u} [Fintype α] [LinearOrder α]

@[simp] theorem toFinset_values (s : EnumerationSource α) :
    s.values.toFinset = Finset.univ := by
  ext a
  simp [s.complete]

@[simp] theorem length_values (s : EnumerationSource α) :
    s.values.length = Fintype.card α := by
  rw [← List.toFinset_card_of_nodup s.nodup, toFinset_values, Finset.card_univ]

/-- Sorting an arbitrary valid enumeration prepares exactly the old table order. -/
theorem prepared_eq_enumerateValues (s : EnumerationSource α) :
    (sortCounted s.values).values =
      Counting.Algorithm.VariableElimination.enumerateValues α := by
  rw [values_sortCounted]
  have hn := (List.perm_insertionSort (· ≤ ·) s.values).nodup_iff.mpr s.nodup
  have hp := List.pairwise_insertionSort (· ≤ ·) s.values
  have he := (List.toFinset_sort (· ≤ ·) hn).mpr hp
  have hs : (s.values.insertionSort (· ≤ ·)).toFinset = Finset.univ := by
    ext a
    simp [List.mem_insertionSort, s.complete]
  rw [hs] at he
  exact he.symm

end EnumerationSource

end Counting.Algorithm.VariableEliminationLayout
