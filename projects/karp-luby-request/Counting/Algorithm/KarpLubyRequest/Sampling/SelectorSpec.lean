import Counting.Algorithm.KarpLubyRequest.Sampling.RowSemantics
import Counting.Algorithm.KarpLuby.Program

/-!
# Stored-row interval selection and occurrence ownership

The scanner keeps skipped rows in reverse order. Its rank is local to the
remaining interval; neither history reversal nor repeated rows changes the
original tagged occurrence selected by `Program.select`.

These are semantic equations for the scanner's exact result. Finite control,
serialized execution and costs are separate obligations.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.SelectorSpec
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine
open RowSemantics

structure Result where
  selected : Bool
  remaining : List Cells
  rank : ℕ
  row : Cells
  prior : List Cells

/-- Scan consecutive mass intervals, retaining every skipped occurrence. -/
def seek : List Cells → ℕ → List Cells → Result
  | [], r, prior => ⟨false, [], r, [], prior⟩
  | row :: rest, r, prior =>
      if r < 2 ^ free row then ⟨true, rest, r, row, prior⟩
      else seek rest (r - 2 ^ free row) (row :: prior)

theorem prior_length_le (rows : List Cells) (r : ℕ) (prior : List Cells) :
    prior.length ≤ (seek rows r prior).prior.length := by
  induction rows generalizing r prior with
  | nil => exact Nat.le_refl _
  | cons row rest ih =>
    by_cases h : r < 2 ^ free row
    · simp only [seek, if_pos h]
      exact Nat.le_refl _
    · simp only [seek, if_neg h]
      exact (Nat.le_succ prior.length).trans (ih (r - 2 ^ free row) (row :: prior))

theorem prior_length_bound (rows : List Cells) (r : ℕ) (prior : List Cells) :
    (seek rows r prior).prior.length ≤ rows.length + prior.length := by
  induction rows generalizing r prior with
  | nil => simp only [seek, List.length_nil, Nat.zero_add, le_refl]
  | cons row rest ih =>
    by_cases h : r < 2 ^ free row
    · simp only [seek, if_pos h, List.length_cons]
      omega
    · simp only [seek, if_neg h, List.length_cons]
      have hb := ih (r - 2 ^ free row) (row :: prior)
      simp only [List.length_cons] at hb
      omega

/-- The stored history is exactly the reversed prefix of skipped occurrences. -/
theorem selected_decomposition (rows : List Cells) (r : ℕ) (prior : List Cells)
    (hs : (seek rows r prior).selected = true) :
    ∃ before : List Cells,
      rows = before ++ (seek rows r prior).row :: (seek rows r prior).remaining ∧
      (seek rows r prior).prior = before.reverse ++ prior := by
  induction rows generalizing r prior with
  | nil => simp only [seek, Bool.false_eq_true] at hs
  | cons row rest ih =>
    by_cases h : r < 2 ^ free row
    · refine ⟨[], ?_, ?_⟩ <;> simp only [seek, if_pos h, List.nil_append, List.reverse_nil]
    · have ht : (seek rest (r - 2 ^ free row) (row :: prior)).selected = true := by
        simpa only [seek, if_neg h] using hs
      obtain ⟨before, hb, hp⟩ := ih (r - 2 ^ free row) (row :: prior) ht
      refine ⟨row :: before, ?_, ?_⟩
      · simpa only [seek, if_neg h, List.cons_append] using congrArg (List.cons row) hb
      · simpa only [seek, if_neg h, List.reverse_cons, List.append_assoc,
          List.singleton_append] using hp

theorem selected_row_length (n : ℕ) (rows : List Cells) (r : ℕ) (prior : List Cells)
    (hlen : ∀ row ∈ rows, row.length = n)
    (hs : (seek rows r prior).selected = true) :
    (seek rows r prior).row.length = n := by
  obtain ⟨before, hb, _⟩ := selected_decomposition rows r prior hs
  have hm : (seek rows r prior).row ∈
      before ++ (seek rows r prior).row :: (seek rows r prior).remaining := by simp
  exact hlen _ (by simpa only [← hb] using hm)

theorem clauseMass_denote (n : ℕ) (row : Cells) (hlen : row.length = n) :
    DNF.clauseMass (DenseNormalization.denote n row) = 2 ^ free row := by
  rw [← hlen, DNF.clauseMass, free_denote]

/-- Exact old selector, including padding rejection and the occurrence index.
An arbitrary pre-existing history contributes no new source occurrence. -/
theorem select_seek (n : ℕ) (rows : List Cells) (r : ℕ) (prior : List Cells)
    (hlen : ∀ row ∈ rows, row.length = n) :
    Program.select (rows.map (DenseNormalization.denote n)) r =
      if (seek rows r prior).selected then
        some ((seek rows r prior).prior.length - prior.length,
          DNF.sampleNat (DenseNormalization.denote n (seek rows r prior).row)
            (seek rows r prior).rank)
      else none := by
  induction rows generalizing r prior with
  | nil => simp only [List.map_nil, Program.select_nil, seek, Bool.false_eq_true, ↓reduceIte]
  | cons row rest ih =>
    have hr : row.length = n := hlen row (by simp only [List.mem_cons, true_or])
    have ht : ∀ c ∈ rest, c.length = n := fun c hc => hlen c (List.mem_cons_of_mem _ hc)
    rw [List.map_cons, Program.select, clauseMass_denote n row hr]
    by_cases h : r < 2 ^ free row
    · simp only [if_pos h, seek, Nat.sub_self, ↓reduceIte]
    · rw [if_neg h, ih (r - 2 ^ free row) (row :: prior) ht]
      simp only [seek, if_neg h]
      cases hs : (seek rest (r - 2 ^ free row) (row :: prior)).selected with
      | false => simp only [hs, Bool.false_eq_true, ↓reduceIte, Option.map_none]
      | true =>
        have hp := prior_length_le rest (r - 2 ^ free row) (row :: prior)
        have hi :
            (seek rest (r - 2 ^ free row) (row :: prior)).prior.length -
                (row :: prior).length + 1 =
              (seek rest (r - 2 ^ free row) (row :: prior)).prior.length - prior.length := by
          simp only [List.length_cons] at hp ⊢
          omega
        simp only [hs, ↓reduceIte, Option.map_some, hi]

/-- Reverse history implements the original prefix owner test for every
assignment. Repeated clauses remain distinct occurrences throughout. -/
theorem owner_seek (n : ℕ) (rows : List Cells) (r : ℕ)
    (hs : (seek rows r []).selected = true) (a : DNF.Assignment n) :
    Program.owner (rows.map (DenseNormalization.denote n))
        (seek rows r []).prior.length a =
      !((seek rows r []).prior.map (DenseNormalization.denote n)).any
        (fun c => DNF.evalClause c a) := by
  obtain ⟨before, hb, hp⟩ := selected_decomposition rows r [] hs
  have hi : (seek rows r []).prior.length = before.length := by
    simp only [hp, List.append_nil, List.length_reverse]
  have htake : rows.take (seek rows r []).prior.length = before := by
    rw [hi, hb, List.take_left]
  unfold Program.owner
  rw [← List.map_take, htake, hp]
  simp only [List.append_nil, List.map_reverse, List.any_reverse]

end Counting.Algorithm.KarpLubyRequest.Sampling.SelectorSpec
