import Counting.Algorithm.KarpLubyRequest.Dense.NormalizeProgram
import Counting.Algorithm.KarpLubyRequest.Dense.NormalizeSemantics

/-! # Exact executions of the term normalizer's preparation and literal call -/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Normalize
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

private theorem header_view (original source raw : List Bool) :
    tapes original source [] raw [] [] [] [] =
      tapes3 (tapes original [] [] [] [] [] [] []) (1 : Fin 8) 3 6 source raw [] := by
  funext k; fin_cases k <;> simp [tapes, tapes3]

private theorem reverse_view (original source stream scratch : List Bool) :
    tapes original source [] [] [] [] scratch stream =
      ReverseFrames.tapes reverseStacks (tapes original [] [] [] [] [] [] []) source stream scratch := by
  funext k; fin_cases k <;> simp [tapes, ReverseFrames.tapes, tapes3]

private theorem allocate_view (original work row scratch stream : List Bool) :
    tapes original [] row work [] [] scratch stream =
      Allocate.tapes allocateStacks (tapes [] [] [] [] [] [] [] stream) original work row scratch := by
  funext k; fin_cases k <;> simp [tapes, Allocate.tapes]

private theorem extract_view (original source row scratch stream : List Bool) :
    tapes original source row [] [] [] scratch stream =
      tapes3 (tapes original [] row [] [] [] [] []) (7 : Fin 8) 1 6 stream source scratch := by
  funext k; fin_cases k <;> simp [tapes, tapes3]

private theorem literal_view (original source row raw counter pref scratch stream : List Bool) :
    tapes original source row raw counter pref scratch stream =
      LiteralWrite.tapes literalStacks (tapes original [] [] [] [] [] [] stream)
        source row raw counter pref scratch := by
  funext k; fin_cases k <;> simp [tapes, LiteralWrite.tapes]

variable {τ : Type} (old : Bool) (memory : τ)

/-- Discarding the raw length header is charged physically; validity and its
relation to the occurrence count have already been proved by the parser. -/
theorem header_exact (original header payload : List Bool) :
    RunsExactly (TM2.step (program (τ := τ)))
      (cfg .headerScan (old, memory) (tapes original (Encoding.frame header ++ payload) [] [] [] [] [] []))
      (cfg .reverseCheck (old, memory) (tapes original payload [] [] [] [] [] []))
      (3 * header.length + 3) := by
  have r1 : RunsExactly (TM2.step (program (τ := τ)))
      (cfg .headerScan (old, memory) (tapes original (Encoding.frame header ++ payload) [] [] [] [] [] []))
      (cfg .headerClear (old, memory) (tapes original payload [] header [] [] [] []))
      (2 * (header.length + 1)) := by
    simpa only [← header_view, Contract.frame_eq, List.append_nil] using
      Frame.extract_exact (1 : Fin 8) 3 6 (by decide) (by decide) (by decide)
        (TM2.step (program (τ := τ))) .headerScan .headerRestore .headerClear .bad
        (by intro state tape; rfl) (by intro state tape; rfl)
        (old, memory) (tapes original [] [] [] [] [] [] []) header payload []
  have r2 := clear_exact (TM2.step (program (τ := τ))) (3 : Fin 8) .headerClear .reverseCheck
    (by intro state tape; rfl) (old, memory) (tapes original payload [] header [] [] [] [])
  have hu : Function.update (tapes original payload [] header [] [] [] []) (3 : Fin 8) [] =
      tapes original payload [] [] [] [] [] [] := by
    funext k; fin_cases k <;> simp [tapes]
  simp only [hu] at r2
  change RunsExactly _ _ _ (header.length + 1) at r2
  convert r1.trans r2 using 1 <;> omega

theorem reverse_exact (original : List Bool) (words : List (List Bool)) :
    RunsExactly (TM2.step (program (τ := τ)))
      (cfg .reverseCheck (old, memory) (tapes original (Encoding.frames words) [] [] [] [] [] []))
      (cfg .allocateCopy (old, memory) (tapes original [] [] [] [] [] [] (Encoding.frames words.reverse)))
      (2 * (words.map List.length).sum + 4 * words.length + 1) := by
  simpa only [← reverse_view, reverseLabels, List.append_nil] using
    ReverseFrames.reverse_exact (TM2.step (program (τ := τ))) reverseStacks reverseLabels executes_reverse
      (old, memory) (tapes original [] [] [] [] [] [] []) words []

theorem allocate_exact (original stream : List Bool) :
    RunsExactly (TM2.step (program (τ := τ)))
      (cfg .allocateCopy (old, memory) (tapes original [] [] [] [] [] [] stream))
      (cfg .loop (old, memory) (tapes original []
        (CellCodec.encode (DenseNormalization.allocate original.length).value) [] [] [] [] stream))
      (3 * original.length + 3) := by
  simpa only [← allocate_view, allocateLabels, List.append_nil] using
    Allocate.allocate_exact (TM2.step (program (τ := τ))) allocateStacks allocateLabels executes_allocate
      (old, memory) (tapes [] [] [] [] [] [] [] stream) original []

theorem prepare_exact (original header : List Bool) (words : List (List Bool)) :
    RunsExactly (TM2.step (program (τ := τ)))
      (cfg .headerScan (old, memory)
        (tapes original (Encoding.frame header ++ Encoding.frames words) [] [] [] [] [] []))
      (cfg .loop (old, memory)
        (tapes original [] (CellCodec.encode (DenseNormalization.allocate original.length).value)
          [] [] [] [] (Encoding.frames words.reverse)))
      (3 * header.length + 2 * (words.map List.length).sum + 4 * words.length +
        3 * original.length + 7) := by
  have r1 := header_exact old memory original header (Encoding.frames words)
  have r2 := reverse_exact old memory original words
  have r3 := allocate_exact old memory original (Encoding.frames words.reverse)
  convert (r1.trans r2).trans r3 using 1 <;> omega

theorem loop_nil_step (original row : List Bool) :
    TM2.step (program (τ := τ)) (cfg .loop (old, memory) (tapes original [] row [] [] [] [] [])) =
      some (cfg .good (old, memory) (tapes original [] row [] [] [] [] [])) := by
  simp [TM2.step, program, cfg, ReverseFrames.checkStmt, TM2.stepAux, tapes]

theorem loop_frame_step (original row word rest : List Bool) :
    TM2.step (program (τ := τ))
      (cfg .loop (old, memory) (tapes original [] row [] [] [] [] (Encoding.frame word ++ rest))) =
      some (cfg .extractScan (old, memory)
        (tapes original [] row [] [] [] [] (Encoding.frame word ++ rest))) := by
  cases word <;> simp [TM2.step, program, cfg, ReverseFrames.checkStmt, TM2.stepAux, tapes, Encoding.frame]

theorem extract_exact (original row word rest : List Bool) :
    RunsExactly (TM2.step (program (τ := τ)))
      (cfg .loop (old, memory) (tapes original [] row [] [] [] [] (Encoding.frame word ++ rest)))
      (cfg .literalScan (old, memory) (tapes original word row [] [] [] [] rest))
      (2 * word.length + 3) := by
  have r1 := runsExactly_one (loop_frame_step old memory original row word rest)
  have r2 : RunsExactly (TM2.step (program (τ := τ)))
      (cfg .extractScan (old, memory) (tapes original [] row [] [] [] [] (Encoding.frame word ++ rest)))
      (cfg .literalScan (old, memory) (tapes original word row [] [] [] [] rest))
      (2 * (word.length + 1)) := by
    simpa only [← extract_view, Contract.frame_eq, List.append_nil] using
      Frame.extract_exact (7 : Fin 8) 1 6 (by decide) (by decide) (by decide)
        (TM2.step (program (τ := τ))) .extractScan .extractRestore .literalScan .bad
        (by intro state tape; rfl) (by intro state tape; rfl)
        (old, memory) (tapes original [] row [] [] [] [] []) word rest []
  convert r1.trans r2 using 1 <;> omega

/-- Intermediate row outcome: another loop iteration on success, physical
remaining-stream cleanup on failure. -/
def afterLiteral (bit : Bool) (memory : τ) (original rest : List Bool)
    (result : Option CellCodec.Cells) : Cfg (Fin 8) Label (Bool × τ) :=
  match result with
  | none => cfg .rejectClear (bit, memory) (tapes original [] [] [] [] [] [] rest)
  | some row => cfg .loop (bit, memory) (tapes original [] (CellCodec.encode row) [] [] [] [] rest)

theorem literal_exact (original rest : List Bool) (l : RawLiteral) (row : CellCodec.Cells) :
    ∃ time : ℕ,
      time ≤ 8 * l.1.length + 16 + (row.length + 1) * (2 * l.1.length + 8) ∧
      RunsExactly (TM2.step (program (τ := τ)))
        (cfg .loop (old, memory)
          (tapes original [] (CellCodec.encode row) [] [] [] [] (Encoding.frame (literalWord l) ++ rest)))
        (afterLiteral l.2 memory original rest (DenseNormalization.write (decodeNat l.1) l.2 row).value) time := by
  have extract := extract_exact old memory original (CellCodec.encode row) (literalWord l) rest
  obtain ⟨time, bound, run⟩ := LiteralWrite.literal_returns (TM2.step (program (τ := τ)))
    literalStacks literalLabels executes_literal old memory (tapes original [] [] [] [] [] [] rest)
    l.1 l.2 row
  have out : LiteralWrite.finished literalStacks literalLabels l.2 memory
      (tapes original [] [] [] [] [] [] rest) (DenseNormalization.write (decodeNat l.1) l.2 row).value =
      afterLiteral l.2 memory original rest (DenseNormalization.write (decodeNat l.1) l.2 row).value := by
    cases (DenseNormalization.write (decodeNat l.1) l.2 row).value <;>
      simp only [LiteralWrite.finished, afterLiteral, literalLabels, writeLabels, ← literal_view]
  rw [out] at run
  simp only [← literal_view] at run
  refine ⟨time + (2 * (literalWord l).length + 3), ?_, extract.trans run⟩
  simp only [literalWord, List.length_append, Encoding.frame_length, List.length_singleton]
  nlinarith

theorem reject_exact (original rest : List Bool) :
    RunsExactly (TM2.step (program (τ := τ)))
      (cfg .rejectClear (old, memory) (tapes original [] [] [] [] [] [] rest))
      (cfg .bad (old, memory) (tapes original [] [] [] [] [] [] []))
      (rest.length + 1) := by
  have run := clear_exact (TM2.step (program (τ := τ))) (7 : Fin 8) .rejectClear .bad
    (by intro state tape; rfl) (old, memory) (tapes original [] [] [] [] [] [] rest)
  have hu : Function.update (tapes original [] [] [] [] [] [] rest) (7 : Fin 8) [] =
      tapes original [] [] [] [] [] [] [] := by
    funext k; fin_cases k <;> simp [tapes]
  rw [hu] at run
  simpa [tapes] using run

end Counting.Algorithm.KarpLubyRequest.Dense.Normalize
