import Counting.Algorithm.KarpLubyRequest.Preparation.Bank

/-! Exact physical cross-bank copies, tuple extraction and frame emission. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing FixedFieldMachines

set_option backward.isDefEq.respectTransparency false

theorem copy_distinct (j : CopyJob) :
    copySource j ≠ copyDestination j ∧ copySource j ≠ scratch ∧ copyDestination j ≠ scratch := by
  cases j <;> constructor
  all_goals first
    | constructor <;> intro h <;> cases h
    | intro h; cases h

/-- A retained copy between the displayed banks. Both scans and the boundary
transitions are counted, and every other stack retains its original contents. -/
theorem copy_run (j : CopyJob) (memory : Memory) (frame : Stack → List Bool)
    (hd : frame (copyDestination j) = []) (hs : frame scratch = []) :
    RunsExactly computer.step (cfg (.copyMove j) memory frame)
      (cfg (copyNext j) memory (Function.update frame (copyDestination j) (frame (copySource j))))
      (2 * (frame (copySource j)).length + 2) :=
  Embedded.copy_into (copySource j) (copyDestination j) scratch
    (copy_distinct j).1 (copy_distinct j).2.1 (copy_distinct j).2.2
    computer.step (.copyMove j) (.copyRestore j) (copyNext j)
    (by intro m t; rfl) (by intro m t; rfl) memory frame hd hs

/-- A discarded reciprocal is really unframed and then cleared. Its complete
payload, including nonempty high-bit words, is charged before the next field. -/
theorem drop_frame (k : Fin 2) (memory : Memory) (frame : Stack → List Bool)
    (word rest out : List Bool) :
    RunsExactly computer.step
      (cfg (.dropScan k) memory
        (tapes3 frame countOutput output scratch (Holant.Algebraic.frame word ++ rest) out []))
      (cfg (dropNext k) memory (tapes3 frame countOutput output scratch rest out []))
      (2 * word.length + 2) := by
  have hs := Frame.scan_exact countOutput output scratch (by intro h; cases h)
    (by intro h; cases h) computer.step (.dropScan k) (.dropClear k) .zero
    (by intro m t; rfl) memory frame word rest out []
  simp only [List.append_nil] at hs
  have hc := clear_exact_update computer.step scratch (.dropClear k) (dropNext k)
    (by intro m t; rfl) memory
    (Function.update (Function.update frame countOutput rest) output out) word.reverse
  simp only [List.length_reverse] at hc
  convert hs.trans hc using 1 <;> first | rfl | omega

/-- The third tuple component is unframed into the actual sample-count stack. -/
theorem sample_extract (memory : Memory) (frame : Stack → List Bool)
    (word rest : List Bool) :
    RunsExactly computer.step
      (cfg .sampleScan memory (tapes3 frame countOutput (budgetOriginal 0) scratch
        (Holant.Algebraic.frame word ++ rest) [] []))
      (cfg .groupMove memory (tapes3 frame countOutput (budgetOriginal 0) scratch rest word []))
      (2 * (word.length + 1)) := by
  have h := Frame.extract_exact countOutput (budgetOriginal 0) scratch
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    computer.step .sampleScan .sampleRestore .groupMove .zero
    (by intro m t; rfl) (by intro m t; rfl) memory frame word rest []
  simpa only [List.append_nil] using h

/-- The unframed group-count tail is moved by two real reversals, so canonical
least-significant-first bit order is retained in the budget bank. -/
theorem group_transfer (memory : Memory) (frame : Stack → List Bool) (word : List Bool) :
    RunsExactly computer.step
      (cfg .groupMove memory (tapes3 frame countOutput (budgetOriginal 1) scratch word [] []))
      (cfg (.copyMove .mass) memory (tapes3 frame countOutput (budgetOriginal 1) scratch [] word []))
      (2 * word.length + 2) := by
  have hm := copy_move_exact countOutput (budgetOriginal 1) scratch
    (by intro h; cases h) (by intro h; cases h) computer.step .groupMove .groupRestore
    (by intro m t; rfl) memory frame word [] []
  simp only [List.append_nil] at hm
  have hr := Frame.restore_exact countOutput (budgetOriginal 1) scratch (by intro h; cases h)
    computer.step .groupRestore (.copyMove .mass) (by intro m t; rfl)
    memory frame [] [] word.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  convert hm.trans hr using 1 <;> omega

/-- The original random tail is physically moved into the output before any
header is emitted. There is no extra frame around this tail. -/
theorem tape_transfer (memory : Memory) (frame : Stack → List Bool) (word : List Bool) :
    RunsExactly computer.step
      (cfg .tapeMove memory (tapes3 frame (budgetOriginal 3) output scratch word [] []))
      (cfg (.emitMove 0) memory (tapes3 frame (budgetOriginal 3) output scratch [] word []))
      (2 * word.length + 2) := by
  have hm := copy_move_exact (budgetOriginal 3) output scratch
    (by intro h; cases h) (by intro h; cases h) computer.step .tapeMove .tapeRestore
    (by intro m t; rfl) memory frame word [] []
  simp only [List.append_nil] at hm
  have hr := Frame.restore_exact (budgetOriginal 3) output scratch (by intro h; cases h)
    computer.step .tapeRestore (.emitMove 0) (by intro m t; rfl)
    memory frame [] [] word.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  convert hm.trans hr using 1 <;> omega

theorem emit_distinct (k : Fin 4) :
    emitSource k ≠ output ∧ emitSource k ≠ scratch ∧ output ≠ scratch := by
  fin_cases k <;> constructor
  all_goals first
    | constructor <;> intro h <;> cases h
    | intro h; cases h

/-- Every payload header is emitted by the unique H1 framing source. -/
theorem emit_frame (k : Fin 4) (memory : Memory) (frame : Stack → List Bool)
    (word rest : List Bool) :
    RunsExactly computer.step
      (cfg (.emitMove k) memory (tapes3 frame (emitSource k) output scratch word rest []))
      (cfg (emitNext k) memory
        (tapes3 frame (emitSource k) output scratch [] (Holant.Algebraic.frame word ++ rest) []))
      (2 * word.length + 3) :=
  FrameEmit.prepend_exact (emitSource k) output scratch
    (emit_distinct k).1 (emit_distinct k).2.1 (emit_distinct k).2.2
    computer.step (.emitMove k) (.emitDelimiter k) (.emit k) (emitNext k)
    (by intro m t; rfl) (by intro m t; rfl) (by intro m t; rfl)
    memory frame word rest

end
end Counting.Algorithm.KarpLubyRequest.Preparation
