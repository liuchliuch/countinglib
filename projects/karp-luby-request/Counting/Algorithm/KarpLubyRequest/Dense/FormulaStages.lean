import Counting.Algorithm.KarpLubyRequest.Dense.FormulaCountCall

/-! # Charged physical copy, term extraction, row emission, and order restoration -/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Formula
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open FixedFieldMachines
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

private theorem copy_view (original formula work : List Bool) :
    tapes3 (bank original [] [] [] [] [] [] []) (8 : Fin 13) 9 6 formula work [] =
      bank original formula work [] [] [] [] [] := by
  funext k; fin_cases k <;> simp [tapes3, bank]

private theorem extract_view (original formula work raw reverseRows tokens output : List Bool) :
    tapes3 (bank original formula [] [] [] reverseRows tokens output) (9 : Fin 13) 1 6 work raw [] =
      bank original formula work raw [] reverseRows tokens output := by
  funext k; fin_cases k <;> simp [tapes3, bank]

private theorem emit_view (original formula work row reverseRows tokens output : List Bool) :
    tapes3 (bank original formula work [] [] [] tokens output) (2 : Fin 13) 10 6 row reverseRows [] =
      bank original formula work [] row reverseRows tokens output := by
  funext k; fin_cases k <;> simp [tapes3, bank]

@[simp] theorem reverseStacks_0 : reverseStacks 0 = 10 := rfl
@[simp] theorem reverseStacks_1 : reverseStacks 1 = 12 := rfl
@[simp] theorem reverseStacks_2 : reverseStacks 2 = 6 := rfl

private theorem reverse_view (original formula reverseRows tokens output : List Bool) :
    ReverseFrames.tapes reverseStacks (bank original formula [] [] [] [] tokens []) reverseRows output [] =
      bank original formula [] [] [] reverseRows tokens output := by
  funext k; fin_cases k <;> simp [ReverseFrames.tapes, tapes3, bank]

variable (bit : Bool)

theorem copy_exact (original formula : List Bool) :
    RunsExactly computer.step
      (cfg .copy (cleanMemory bit) (bank original formula [] [] [] [] [] []))
      (cfg .headerScan (cleanMemory bit) (bank original formula formula [] [] [] [] []))
      (2 * (formula.length + 1)) := by
  simpa only [copy_view, List.append_nil] using
    copy_exact_frame (8 : Fin 13) 9 6 (by decide) (by decide) (by decide)
      computer.step .copy .copyRestore .headerScan (by intro state tape; rfl) (by intro state tape; rfl)
      (cleanMemory bit) (bank original [] [] [] [] [] [] []) formula []

theorem header_exact (original formula header payload : List Bool) :
    RunsExactly computer.step
      (cfg .headerScan (cleanMemory bit) (bank original formula (Encoding.frame header ++ payload) [] [] [] [] []))
      (cfg .loop (cleanMemory bit) (bank original formula payload [] [] [] [] []))
      (3 * header.length + 3) := by
  let base := bank original formula [] [] [] [] [] []
  have scan := Frame.extract_exact (9 : Fin 13) 3 6 (by decide) (by decide) (by decide)
    computer.step .headerScan .headerRestore .headerClear .bad
    (by intro state tape; rfl) (by intro state tape; rfl) (cleanMemory bit) base header payload []
  have clear := clear_exact computer.step (3 : Fin 13) .headerClear .loop
    (by intro state tape; rfl) (cleanMemory bit) (tapes3 base 9 3 6 payload header [])
  have start : tapes3 base (9 : Fin 13) 3 6 (Encoding.frame header ++ payload) [] [] =
      bank original formula (Encoding.frame header ++ payload) [] [] [] [] [] := by
    funext k; fin_cases k <;> simp [tapes3, base, bank]
  have stop : Function.update (tapes3 base (9 : Fin 13) 3 6 payload header []) 3 [] =
      bank original formula payload [] [] [] [] [] := by
    funext k; fin_cases k <;> simp [tapes3, base, bank]
  simp only [← Contract.frame_eq, List.append_nil, start] at scan
  rw [stop] at clear
  have len : (tapes3 base (9 : Fin 13) 3 6 payload header [] 3).length = header.length := by simp [tapes3]
  rw [len] at clear
  convert scan.trans clear using 1 <;> omega

theorem loop_nil (original formula reverseRows tokens output : List Bool) :
    computer.step (cfg .loop (cleanMemory bit) (bank original formula [] [] [] reverseRows tokens output)) =
      some (cfg .reverseCheck (cleanMemory bit) (bank original formula [] [] [] reverseRows tokens output)) := by
  simp [FinTM2.step, TM2.step, program, cfg, ReverseFrames.checkStmt, TM2.stepAux, bank]
  rfl

theorem loop_frame (original formula raw rest reverseRows tokens output : List Bool) :
    computer.step (cfg .loop (cleanMemory bit)
      (bank original formula (Encoding.frame raw ++ rest) [] [] reverseRows tokens output)) =
      some (cfg .extractScan (cleanMemory bit)
        (bank original formula (Encoding.frame raw ++ rest) [] [] reverseRows tokens output)) := by
  cases raw <;> simp [FinTM2.step, TM2.step, program, cfg, ReverseFrames.checkStmt, TM2.stepAux, bank, Encoding.frame] <;> rfl

theorem extract_exact (original formula raw rest reverseRows tokens output : List Bool) :
    RunsExactly computer.step
      (cfg .loop (cleanMemory bit) (bank original formula (Encoding.frame raw ++ rest) [] [] reverseRows tokens output))
      (cfg (.term .headerScan) (cleanMemory bit) (bank original formula rest raw [] reverseRows tokens output))
      (2 * raw.length + 3) := by
  have first := runsExactly_one (loop_frame bit original formula raw rest reverseRows tokens output)
  have scan := Frame.extract_exact (9 : Fin 13) 1 6 (by decide) (by decide) (by decide)
    computer.step .extractScan .extractRestore (.term .headerScan) .bad
    (by intro state tape; rfl) (by intro state tape; rfl) (cleanMemory bit)
    (bank original formula [] [] [] reverseRows tokens output) raw rest []
  simp only [← Contract.frame_eq, List.append_nil, extract_view] at scan
  convert first.trans scan using 1 <;> omega

theorem drop_step (original formula work reverseRows tokens output : List Bool) :
    computer.step (cfg .afterTerm (cleanMemory false) (bank original formula work [] [] reverseRows tokens output)) =
      some (cfg .loop (cleanMemory false) (bank original formula work [] [] reverseRows tokens output)) := by rfl

theorem keep_exact (original formula work : List Bool) (row : CellCodec.Cells)
    (reverseRows tokens output : List Bool) :
    RunsExactly computer.step
      (cfg .afterTerm (cleanMemory true) (bank original formula work [] (CellCodec.encode row) reverseRows tokens output))
      (cfg .loop (cleanMemory true)
        (bank original formula work [] [] (Encoding.frame (CellCodec.encode row) ++ reverseRows) (true :: tokens) output))
      (4 * row.length + 5) := by
  have first : RunsExactly computer.step
      (cfg .afterTerm (cleanMemory true) (bank original formula work [] (CellCodec.encode row) reverseRows tokens output))
      (cfg .emitMove (cleanMemory true) (bank original formula work [] (CellCodec.encode row) reverseRows tokens output)) 1 := by
    apply runsExactly_one; rfl
  have emit := FrameEmit.prepend_exact (2 : Fin 13) 10 6 (by decide) (by decide) (by decide)
    computer.step .emitMove .emitDelimiter .emit .tally
    (by intro state tape; rfl) (by intro state tape; rfl) (by intro state tape; rfl)
    (cleanMemory true) (bank original formula work [] [] [] tokens output) (CellCodec.encode row) reverseRows
  simp only [← Contract.frame_eq, emit_view, CellCodec.encode_length] at emit
  have tally : RunsExactly computer.step
      (cfg .tally (cleanMemory true) (bank original formula work [] []
        (Encoding.frame (CellCodec.encode row) ++ reverseRows) tokens output))
      (cfg .loop (cleanMemory true) (bank original formula work [] []
        (Encoding.frame (CellCodec.encode row) ++ reverseRows) (true :: tokens) output)) 1 := by
    apply runsExactly_one
    simp [FinTM2.step, TM2.step, program, cfg, TM2.stepAux, bank]
    funext k; fin_cases k <;> simp [bank]
  convert (first.trans emit).trans tally using 1 <;> omega

theorem restore_order_exact (original formula : List Bool) (rows : List CellCodec.Cells) (tokens : List Bool) :
    RunsExactly computer.step
      (cfg .reverseCheck (cleanMemory bit) (bank original formula [] [] [] (CellCodec.rows rows) tokens []))
      (cfg (.count 0) (cleanMemory bit) (bank original formula [] [] [] [] tokens (CellCodec.rows rows.reverse)))
      (4 * (rows.map List.length).sum + 4 * rows.length + 1) := by
  have run := ReverseFrames.reverse_exact computer.step reverseStacks reverseLabels executes_reverse
    (cleanMemory bit) (bank original formula [] [] [] [] tokens []) (rows.map CellCodec.encode) []
  have lengths : ((rows.map CellCodec.encode).map List.length).sum = 2 * (rows.map List.length).sum := by
    clear run
    induction rows with
    | nil => rfl
    | cons row rows ih =>
      simp only [List.map_cons, List.sum_cons, CellCodec.encode_length, ih, Nat.mul_add]
  simp only [reverse_view, reverseLabels, List.append_nil, ← List.map_reverse,
    List.length_map, lengths] at run
  convert run using 1 <;> first | rfl | omega

end Counting.Algorithm.KarpLubyRequest.Dense.Formula
