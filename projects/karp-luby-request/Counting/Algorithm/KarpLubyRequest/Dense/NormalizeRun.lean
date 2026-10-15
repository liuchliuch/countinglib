import Counting.Algorithm.KarpLubyRequest.Dense.NormalizeStages

/-! # Physical occurrence loop and exact tail-first term normalization -/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Normalize
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

def indexBits (words : List RawLiteral) : ℕ := (words.map (fun l => l.1.length)).sum

def loopCost (n : ℕ) (words : List RawLiteral) : ℕ :=
  8 * indexBits words + 16 * words.length + (n + 1) * (2 * indexBits words + 8 * words.length) + 1

@[simp] theorem indexBits_nil : indexBits [] = 0 := rfl
@[simp] theorem indexBits_cons (l : RawLiteral) (ls : List RawLiteral) :
    indexBits (l :: ls) = l.1.length + indexBits ls := rfl

@[simp] theorem loopCost_nil (n : ℕ) : loopCost n [] = 1 := by simp [loopCost]

theorem loopCost_cons (n : ℕ) (l : RawLiteral) (ls : List RawLiteral) :
    loopCost n (l :: ls) =
      (8 * l.1.length + 16 + (n + 1) * (2 * l.1.length + 8)) + loopCost n ls := by
  simp only [loopCost, indexBits_cons, List.length_cons]
  ring

theorem framedWords_length (words : List RawLiteral) :
    (Encoding.frames (words.map literalWord)).length = 4 * indexBits words + 5 * words.length := by
  induction words with
  | nil => rfl
  | cons l words ih =>
    simp only [List.map_cons, Encoding.frames, List.length_append, Encoding.frame_length,
      literalWord, List.length_singleton, ih, indexBits_cons, List.length_cons, List.length_nil]
    ring

theorem cleanup_le_loopCost (n : ℕ) (words : List RawLiteral) :
    (Encoding.frames (words.map literalWord)).length + 1 ≤ loopCost n words := by
  rw [framedWords_length, loopCost]
  omega

/-- Every work stack is empty on return apart from the successful row. The
original unary word remains present even for a contradictory term. -/
def finished {τ : Type} (bit : Bool) (memory : τ) (original : List Bool)
    (result : Option CellCodec.Cells) : Cfg (Fin 8) Label (Bool × τ) :=
  match result with
  | none => cfg .bad (bit, memory) (tapes original [] [] [] [] [] [] [])
  | some row => cfg .good (bit, memory) (tapes original [] (CellCodec.encode row) [] [] [] [] [])

variable {τ : Type} (old : Bool) (memory : τ)

theorem loop_returns (original : List Bool) (n : ℕ) (words : List RawLiteral)
    (row : CellCodec.Cells) (hrow : row.length = n) :
    ∃ bit : Bool, ∃ time : ℕ, time ≤ loopCost n words ∧
      RunsExactly (TM2.step (program (τ := τ)))
        (cfg .loop (old, memory)
          (tapes original [] (CellCodec.encode row) [] [] [] [] (Encoding.frames (words.map literalWord))))
        (finished bit memory original (rawWrites words (some row))) time := by
  induction words generalizing old row with
  | nil =>
    refine ⟨old, 1, by simp, ?_⟩
    simpa only [List.map_nil, Encoding.frames, rawWrites, writes, finished] using
      runsExactly_one (loop_nil_step old memory original (CellCodec.encode row))
  | cons l words ih =>
    obtain ⟨time, bound, run⟩ := literal_exact old memory original
      (Encoding.frames (words.map literalWord)) l row
    rw [hrow] at bound
    cases hw : (DenseNormalization.write (decodeNat l.1) l.2 row).value with
    | none =>
      rw [hw] at run
      have clean := reject_exact l.2 memory original (Encoding.frames (words.map literalWord))
      have cleanBound := cleanup_le_loopCost n words
      refine ⟨l.2, ((Encoding.frames (words.map literalWord)).length + 1) + time, ?_, ?_⟩
      · rw [loopCost_cons]
        omega
      · simpa only [List.map_cons, Encoding.frames, rawWrites, writes, literalValue,
          Option.bind_some, hw, writes_none, afterLiteral, finished] using run.trans clean
    | some ys =>
      have hy : ys.length = n :=
        (DenseNormalization.write_length row (decodeNat l.1) l.2 ys hw).trans hrow
      obtain ⟨bit, restTime, restBound, restRun⟩ := ih l.2 ys hy
      rw [hw] at run
      refine ⟨bit, restTime + time, ?_, ?_⟩
      · rw [loopCost_cons]
        omega
      · simpa only [List.map_cons, Encoding.frames, rawWrites, writes, literalValue,
          Option.bind_some, hw, afterLiteral] using run.trans restRun

/-- The whole finite program executes the existing normalizer, given the exact
raw literal words obtained from the already checked term decoder. No canonical
index-word restriction and no index-valued control register is used. -/
theorem normalize_prepared (original header : List Bool) (words : List RawLiteral)
    (term : DNF.RawTerm original.length)
    (hwords : words.map literalValue = term.map (fun l => (l.1.val, l.2))) :
    ∃ bit : Bool, ∃ time : ℕ,
      time ≤ 3 * header.length + 2 * ((words.map literalWord).map List.length).sum +
        4 * words.length + 3 * original.length + 7 + loopCost original.length words.reverse ∧
      RunsExactly (TM2.step (program (τ := τ)))
        (cfg .headerScan (old, memory)
          (tapes original (Encoding.frame header ++ Encoding.frames (words.map literalWord)) [] [] [] [] [] []))
        (finished bit memory original (DenseNormalization.normalize original.length term).value) time := by
  have prep := prepare_exact old memory original header (words.map literalWord)
  obtain ⟨bit, time, bound, run⟩ := loop_returns old memory original original.length words.reverse
    (DenseNormalization.allocate original.length).value (by simp)
  rw [rawWrites_normalize term words hwords] at run
  rw [List.map_reverse] at run
  refine ⟨bit, time + (3 * header.length + 2 * ((words.map literalWord).map List.length).sum +
    4 * (words.map literalWord).length + 3 * original.length + 7), ?_, prep.trans run⟩
  simp only [List.length_map]
  omega

end Counting.Algorithm.KarpLubyRequest.Dense.Normalize
