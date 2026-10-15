import Counting.Algorithm.KarpLubyRequest.Dense.FormulaStages

/-! # Complete physical formula traversal with exact multiplicity and order -/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Formula
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

/-- One term's allowance includes its outer frame, full finite normalization,
and either its row emission/count token or its rejection branch. -/
def termCost (n size : ℕ) : ℕ := 10 * n * size + 45 * size + 7 * n + 17

def nextRows (result : Option CellCodec.Cells) (acc : List CellCodec.Cells) : List CellCodec.Cells :=
  result.elim acc (fun row => row :: acc)

def nextTokens (result : Option CellCodec.Cells) (tokens : List Bool) : List Bool :=
  if result.isSome then true :: tokens else tokens

theorem term_exact (old : Bool) (original formula raw rest : List Bool)
    (term : DNF.RawTerm original.length)
    (hdecode : (Encoding.list (Encoding.literal original.length)).decode raw = some term)
    (acc : List CellCodec.Cells) (tokens output : List Bool) :
    ∃ time : ℕ, time ≤ termCost original.length raw.length ∧
      RunsExactly computer.step
        (cfg .loop (cleanMemory old)
          (bank original formula (Encoding.frame raw ++ rest) [] [] (CellCodec.rows acc) tokens output))
        (cfg .loop (cleanMemory (DenseNormalization.normalize original.length term).value.isSome)
          (bank original formula rest [] []
            (CellCodec.rows (nextRows (DenseNormalization.normalize original.length term).value acc))
            (nextTokens (DenseNormalization.normalize original.length term).value tokens) output)) time := by
  have extract := extract_exact old original formula raw rest (CellCodec.rows acc) tokens output
  obtain ⟨time, bound, call⟩ := term_call old original formula rest raw (CellCodec.rows acc) tokens output term hdecode
  cases hn : (DenseNormalization.normalize original.length term).value with
  | none =>
    simp only [hn, Option.isSome_none, Option.elim_none] at call
    have drop := runsExactly_one (drop_step original formula rest (CellCodec.rows acc) tokens output)
    refine ⟨1 + (time + (2 * raw.length + 3)), ?_, ?_⟩
    · unfold Normalize.rawCost at bound
      unfold termCost
      omega
    · simpa only [hn, nextRows, nextTokens, Option.isSome_none, Option.elim_none, Bool.false_eq_true, ↓reduceIte] using
        (extract.trans call).trans drop
  | some row =>
    simp only [hn, Option.isSome_some, Option.elim_some] at call
    have keep := keep_exact original formula rest row (CellCodec.rows acc) tokens output
    have length := DenseNormalization.normalize_length term row hn
    refine ⟨(4 * row.length + 5) + (time + (2 * raw.length + 3)), ?_, ?_⟩
    · rw [length]
      unfold Normalize.rawCost at bound
      unfold termCost
      omega
    · simpa only [hn, nextRows, nextTokens, Option.isSome_some, Option.elim_some, ↓reduceIte, CellCodec.rows_cons] using
        (extract.trans call).trans keep

def wordBits (raws : List (List Bool)) : ℕ := (raws.map List.length).sum

def loopCost (n : ℕ) (raws : List (List Bool)) : ℕ :=
  10 * n * wordBits raws + 45 * wordBits raws + (7 * n + 17) * raws.length + 1

@[simp] theorem loopCost_nil (n : ℕ) : loopCost n [] = 1 := by simp [loopCost, wordBits]

theorem loopCost_cons (n : ℕ) (raw : List Bool) (raws : List (List Bool)) :
    loopCost n (raw :: raws) = termCost n raw.length + loopCost n raws := by
  simp only [loopCost, termCost, wordBits, List.map_cons, List.sum_cons, List.length_cons]
  ring

/-- Clause multiplicities are retained. The accumulator and its actual unary
count tokens grow once per successful term, never once per distinct clause. -/
theorem loop_returns (old : Bool) (original formula : List Bool) (raws : List (List Bool))
    (terms : DNF.Formula original.length)
    (hdecode : raws.mapM (Encoding.list (Encoding.literal original.length)).decode = some terms)
    (acc : List CellCodec.Cells) :
    ∃ bit : Bool, ∃ time : ℕ, time ≤ loopCost original.length raws ∧
      RunsExactly computer.step
        (cfg .loop (cleanMemory old)
          (bank original formula (Encoding.frames raws) [] [] (CellCodec.rows acc)
            (List.replicate acc.length true) []))
        (cfg .reverseCheck (cleanMemory bit)
          (bank original formula [] [] []
            (CellCodec.rows ((DenseNormalization.formula original.length terms).value.reverse ++ acc))
            (List.replicate ((DenseNormalization.formula original.length terms).value.length + acc.length) true) [])) time := by
  induction raws generalizing old terms acc with
  | nil =>
    have ht : terms = [] := by simpa using hdecode.symm
    subst terms
    refine ⟨old, 1, by simp, ?_⟩
    simpa only [Encoding.frames, DenseNormalization.formula, List.reverse_nil, List.nil_append,
      List.length_nil, Nat.zero_add] using
      runsExactly_one (loop_nil old original formula (CellCodec.rows acc) (List.replicate acc.length true) [])
  | cons raw raws ih =>
    cases hd : (Encoding.list (Encoding.literal original.length)).decode raw with
    | none => simp [List.mapM_cons, hd] at hdecode
    | some term =>
      cases ht : raws.mapM (Encoding.list (Encoding.literal original.length)).decode with
      | none => simp [List.mapM_cons, hd, ht] at hdecode
      | some tail =>
        have he : term :: tail = terms := by simpa [List.mapM_cons, hd, ht] using hdecode
        subst terms
        obtain ⟨time, bound, first⟩ := term_exact old original formula raw (Encoding.frames raws)
          term hd acc (List.replicate acc.length true) []
        cases hn : (DenseNormalization.normalize original.length term).value with
        | none =>
          obtain ⟨bit, restTime, restBound, rest⟩ := ih false tail ht acc
          simp only [hn, nextRows, nextTokens, Option.isSome_none, Option.elim_none, Bool.false_eq_true, ↓reduceIte] at first
          refine ⟨bit, restTime + time, ?_, ?_⟩
          · rw [loopCost_cons]; omega
          · simpa only [Encoding.frames, DenseNormalization.formula, hn] using first.trans rest
        | some row =>
          obtain ⟨bit, restTime, restBound, rest⟩ := ih true tail ht (row :: acc)
          simp only [hn, nextRows, nextTokens, Option.isSome_some, Option.elim_some, ↓reduceIte] at first
          have token : true :: List.replicate acc.length true = List.replicate (row :: acc).length true := by
            simp only [List.length_cons, List.replicate_succ]
          rw [token] at first
          refine ⟨bit, restTime + time, ?_, ?_⟩
          · rw [loopCost_cons]; omega
          · simpa only [Encoding.frames, DenseNormalization.formula, hn, List.reverse_cons,
              List.append_assoc, List.singleton_append, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using
              first.trans rest

end Counting.Algorithm.KarpLubyRequest.Dense.Formula
