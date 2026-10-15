import Counting.Algorithm.KarpLubyRequest.Sampling.SelectorCompare

/-! # Real interval rejection, subtraction and physical history accumulation -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Selector
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing FixedFieldMachines
open Counting.Algorithm.KarpLuby

def finished (selected : Bool) (source rank row mass history : List Bool) : Cfg Stack Label Memory :=
  ⟨none, (none, selected, none, none), tapes source rank row mass [] [] [] [] [] history []⟩

theorem empty_step (rank history : List Bool) :
    computer.step (config 0 [] rank [] [] [] [] [] [] [] history []) =
      some (finished false [] rank [] [] history) := by
  simp [FinTM2.step, TM2.step, program, loop, config, finished, cfg, TM2.stepAux, tapes]
  rfl

theorem selected_step (rest rank row mass history : List Bool) :
    computer.step (config 13 rest rank row mass [] [] [] [] [true] history []) =
      some (finished true rest rank row mass history) := by
  simp [FinTM2.step, TM2.step, program, decideInterval, config, finished, cfg, TM2.stepAux, tapes]
  congr 2; funext k; fin_cases k <;> rfl

theorem rejected_step (rest rank row mass history : List Bool) :
    computer.step (config 13 rest rank row mass [] [] [] [] [false] history []) =
      some (config 14 rest rank row mass [] [] [] [] [] history []) := by
  simp [FinTM2.step, TM2.step, program, decideInterval, config, cfg, TM2.stepAux, tapes]
  congr 2; funext k; fin_cases k <;> rfl

theorem subtraction (r m : ℕ) (rest row history : List Bool) :
    RunsExactly computer.step (config 14 rest (encodeNat r) row (encodeNat m) [] [] [] [] [] history [])
      (config 18 rest [] row [] [] [] [] [] (encodeNat (r - m)) history [])
      (2 * max (encodeNat r).length (encodeNat m).length + 2) := by
  apply MachineCall.run subtractStacks subtractLabel 18 arithmeticState BinaryArithmetic.Subtraction.program
    program subtraction_code none (tapes rest [] row [] [] [] [] [] [] history [])
    (BinaryArithmetic.Subtraction.cfg (some .columns) false (encodeNat r) (encodeNat m) [] [])
    (BinaryArithmetic.Subtraction.cfg none false [] [] [] (encodeNat (r - m)))
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; cases k <;> rfl
    · intro k hk; fin_cases k <;>
        first | rfl | exact False.elim (hk .left rfl) | exact False.elim (hk .right rfl)
              | exact False.elim (hk .work rfl) | exact False.elim (hk .out rfl)
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; cases k <;> rfl
    · intro k hk; fin_cases k <;>
        first | rfl | exact False.elim (hk .left rfl) | exact False.elim (hk .right rfl)
              | exact False.elim (hk .work rfl) | exact False.elim (hk .out rfl)
  · exact BinaryArithmetic.Subtraction.compute_encodeNat_exact r m

private theorem as_move (rest row work output history : List Bool) :
    tapes rest [] row [] [] [] work [] output history [] =
      tapes3 (tapes rest [] [] [] [] [] [] [] [] history []) (8 : Stack) 2 6 output row work := by
  funext k; fin_cases k <;> rfl

private theorem as_restore (rest rank row work history : List Bool) :
    tapes rest rank row [] [] [] work [] [] history [] =
      tapes3 (tapes rest [] [] [] [] [] [] [] [] history []) (6 : Stack) 2 1 work row rank := by
  funext k; fin_cases k <;> rfl

theorem transfer (rest row word history : List Bool) :
    RunsExactly computer.step (config 18 rest [] row [] [] [] [] [] word history [])
      (config 20 rest word row [] [] [] [] [] [] history []) (2 * (word.length + 1)) := by
  have hm : ExecutesAt computer.step (18 : Label) (copyMoveStmt (8 : Stack) 6 18 19) := by
    intro state tape; rfl
  have hr : ExecutesAt computer.step (19 : Label) (copyMoveStmt (6 : Stack) 1 19 20) := by
    intro state tape; rfl
  have h1 : RunsExactly computer.step (config 18 rest [] row [] [] [] [] [] word history [])
      (config 19 rest [] row [] [] [] word.reverse [] [] history []) (word.length + 1) := by
    simpa only [config, ← as_move, List.append_nil] using
      copy_move_exact (8 : Stack) 2 6 (by decide) (by decide) computer.step (18 : Label) 19 hm
        BinaryArithmetic.Addition.initial (tapes rest [] [] [] [] [] [] [] [] history []) word row []
  have h2 : RunsExactly computer.step (config 19 rest [] row [] [] [] word.reverse [] [] history [])
      (config 20 rest word row [] [] [] [] [] [] history []) (word.length + 1) := by
    simpa only [config, ← as_restore, List.append_nil, List.reverse_reverse, List.length_reverse] using
      copy_move_exact (6 : Stack) 2 1 (by decide) (by decide) computer.step (19 : Label) 20 hr
        BinaryArithmetic.Addition.initial (tapes rest [] [] [] [] [] [] [] [] history []) word.reverse row []
  convert h1.trans h2 using 1 <;> omega

private theorem as_emit (rest rank row scratch history : List Bool) :
    tapes rest rank row [] [] [] scratch [] [] history [] =
      tapes3 (tapes rest rank [] [] [] [] [] [] [] [] []) (2 : Stack) 9 6 row history scratch := by
  funext k; fin_cases k <;> rfl

theorem emit (rest rank row history : List Bool) :
    RunsExactly computer.step (config 20 rest rank row [] [] [] [] [] [] history [])
      (config 0 rest rank [] [] [] [] [] [] [] (Encoding.frame row ++ history) [])
      (2 * row.length + 3) := by
  have hm : ExecutesAt computer.step (20 : Label) (copyMoveStmt (2 : Stack) 6 20 21) := by
    intro state tape; rfl
  have hd : ExecutesAt computer.step (21 : Label) (FrameEmit.delimiterStmt (9 : Stack) 22) := by
    intro state tape; rfl
  have he : ExecutesAt computer.step (22 : Label) (FrameEmit.emitStmt (6 : Stack) 9 22 0) := by
    intro state tape; rfl
  simpa only [config, ← as_emit, ← Contract.frame_eq] using
    FrameEmit.prepend_exact (2 : Stack) 9 6 (by decide) (by decide) (by decide)
      computer.step (20 : Label) 21 22 0 hm hd he BinaryArithmetic.Addition.initial
      (tapes rest rank [] [] [] [] [] [] [] [] []) row history

def advanceTime (xs : RowSemantics.Cells) (r : ℕ) : ℕ :=
  2 * max (encodeNat r).length (encodeNat (2 ^ RowSemantics.free xs)).length +
    2 * (encodeNat (r - 2 ^ RowSemantics.free xs)).length + 4 * xs.length + 8

/-- A rejected interval subtracts its mass and physically stores that occurrence. -/
theorem advance_row (xs : RowSemantics.Cells) (r : ℕ) (rest history : List Bool) :
    RunsExactly computer.step
      (config 13 rest (encodeNat r) (Dense.CellCodec.encode xs) (encodeNat (2 ^ RowSemantics.free xs))
        [] [] [] [] [false] history [])
      (config 0 rest (encodeNat (r - 2 ^ RowSemantics.free xs)) [] [] [] [] [] [] []
        (Encoding.frame (Dense.CellCodec.encode xs) ++ history) []) (advanceTime xs r) := by
  have h1 := runsExactly_one (rejected_step rest (encodeNat r) (Dense.CellCodec.encode xs)
    (encodeNat (2 ^ RowSemantics.free xs)) history)
  have h2 := subtraction r (2 ^ RowSemantics.free xs) rest (Dense.CellCodec.encode xs) history
  have h3 := transfer rest (Dense.CellCodec.encode xs) (encodeNat (r - 2 ^ RowSemantics.free xs)) history
  have h4 := emit rest (encodeNat (r - 2 ^ RowSemantics.free xs)) (Dense.CellCodec.encode xs) history
  have hr := ((h1.trans h2).trans h3).trans h4
  convert hr using 1 <;> simp only [advanceTime, Dense.CellCodec.encode_length] <;> omega

end Counting.Algorithm.KarpLubyRequest.Sampling.Selector
