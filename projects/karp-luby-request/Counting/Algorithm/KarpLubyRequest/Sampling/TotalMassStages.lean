import Counting.Algorithm.KarpLubyRequest.Sampling.TotalMassProgram

/-! # The connected extraction, mass, addition and transfer stages -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.TotalMass
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby

private theorem as_frame (source mass total row work output : List Bool) :
    tapes source mass total row work output =
      tapes3 (tapes [] mass total [] [] output) (0 : Stack) 3 4 source row work := by
  funext k; fin_cases k <;> rfl

private theorem as_move (source mass total row work output : List Bool) :
    tapes source mass total row work output =
      tapes3 (tapes source [] total row [] []) (5 : Stack) 1 4 output mass work := by
  funext k; fin_cases k <;> rfl

private theorem as_restore (source mass total row work output : List Bool) :
    tapes source mass total row work output =
      tapes3 (tapes source [] [] row [] output) (4 : Stack) 1 2 work mass total := by
  funext k; fin_cases k <;> rfl

theorem loop_nonempty (bit : Bool) (rest total : List Bool) :
    computer.step (config 0 (bit :: rest) [] total [] [] []) =
      some (config 1 (bit :: rest) [] total [] [] []) := by
  simp [FinTM2.step, TM2.step, program, loop, config, cfg, TM2.stepAux, tapes]
  rfl

theorem loop_empty (total : List Bool) :
    computer.step (config 0 [] [] total [] [] []) = some (finished total) := by
  simp [FinTM2.step, TM2.step, program, loop, config, finished, cfg, TM2.stepAux, tapes]
  rfl

theorem extract (row rest total : List Bool) :
    RunsExactly computer.step (config 0 (Encoding.frame row ++ rest) [] total [] [] [])
      (config 3 rest [] total row [] []) (2 * row.length + 3) := by
  have hc : computer.step (config 0 (Encoding.frame row ++ rest) [] total [] [] []) =
      some (config 1 (Encoding.frame row ++ rest) [] total [] [] []) := by
    cases row with
    | nil => exact loop_nonempty false rest total
    | cons bit word => exact loop_nonempty true (bit :: (Encoding.frame word ++ rest)) total
  have hs : ExecutesAt computer.step (1 : Label) (Frame.scanStmt (0 : Stack) 4 1 2 10) := by
    intro state tape; rfl
  have hr : ExecutesAt computer.step (2 : Label) (copyMoveStmt (4 : Stack) 3 2 3) := by
    intro state tape; rfl
  have he : RunsExactly computer.step (config 1 (Encoding.frame row ++ rest) [] total [] [] [])
      (config 3 rest [] total row [] []) (2 * (row.length + 1)) := by
    simpa only [config, ← as_frame, ← Contract.frame_eq, List.append_nil] using
      Frame.extract_exact (0 : Stack) 3 4 (by decide) (by decide) (by decide)
        computer.step (1 : Label) 2 3 10 hs hr BinaryArithmetic.Addition.initial
        (tapes [] [] total [] [] []) row rest []
  convert (runsExactly_one hc).trans he using 1 <;> omega

/-- The extracted row is consumed by the actual finite row scanner. -/
theorem mass_call (xs : RowSemantics.Cells) (rest total : List Bool) :
    RunsExactly computer.step (config 3 rest [] total (Dense.CellCodec.encode xs) [] [])
      (config 6 rest (encodeNat (2 ^ RowSemantics.free xs)) total [] [] []) (xs.length + 3) := by
  apply MachineCall.run massStacks massLabel 6 massState RowMass.program program mass_code
    BinaryArithmetic.Addition.initial (tapes rest [] total [] [] [])
    (RowMass.config 0 (Dense.CellCodec.encode xs) [])
    (⟨none, (none, ()), RowMass.tapes [] (encodeNat (2 ^ RowSemantics.free xs))⟩)
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro k hk; fin_cases k <;>
        first | rfl | exact False.elim (hk 0 rfl) | exact False.elim (hk 1 rfl)
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro k hk; fin_cases k <;>
        first | rfl | exact False.elim (hk 0 rfl) | exact False.elim (hk 1 rfl)
  · exact RowMass.halt_exact xs

/-- Canonical H1 addition is called on physically prepared operand stacks. -/
theorem addition_call (a b : ℕ) (rest : List Bool) :
    RunsExactly computer.step (config 6 rest (encodeNat b) (encodeNat a) [] [] [])
      (config 8 rest [] [] [] [] (encodeNat (a + b)))
      (max (encodeNat a).length (encodeNat b).length + (encodeNat (a + b)).length + 2) := by
  apply MachineCall.run additionStacks additionLabel 8 additionState BinaryArithmetic.Addition.program
    program addition_code none (tapes rest [] [] [] [] [])
    (BinaryArithmetic.Addition.cfg (some false) false (encodeNat a) (encodeNat b) [] [])
    (BinaryArithmetic.Addition.cfg none false [] [] [] (encodeNat (a + b)))
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
  · exact BinaryArithmetic.Addition.compute_encodeNat_exact a b

/-- The adder's output is moved through two real stack scans to preserve order. -/
theorem transfer (rest word : List Bool) :
    RunsExactly computer.step (config 8 rest [] [] [] [] word)
      (config 0 rest [] word [] [] []) (2 * (word.length + 1)) := by
  have hm : ExecutesAt computer.step (8 : Label) (copyMoveStmt (5 : Stack) 4 8 9) := by
    intro state tape; rfl
  have hr : ExecutesAt computer.step (9 : Label) (copyMoveStmt (4 : Stack) 2 9 0) := by
    intro state tape; rfl
  have h1 : RunsExactly computer.step (config 8 rest [] [] [] [] word)
      (config 9 rest [] [] [] word.reverse []) (word.length + 1) := by
    simpa only [config, ← as_move, List.append_nil] using
      copy_move_exact (5 : Stack) 1 4 (by decide) (by decide) computer.step (8 : Label) 9 hm
        BinaryArithmetic.Addition.initial (tapes rest [] [] [] [] []) word [] []
  have h2 : RunsExactly computer.step (config 9 rest [] [] [] word.reverse [])
      (config 0 rest [] word [] [] []) (word.length + 1) := by
    simpa only [config, ← as_restore, List.append_nil, List.reverse_reverse, List.length_reverse] using
      copy_move_exact (4 : Stack) 1 2 (by decide) (by decide) computer.step (9 : Label) 0 hr
        BinaryArithmetic.Addition.initial (tapes rest [] [] [] [] []) word.reverse [] []
  convert h1.trans h2 using 1 <;> omega

def rowTime (xs : RowSemantics.Cells) (a : ℕ) : ℕ :=
  5 * xs.length + 10 + max (encodeNat a).length (encodeNat (2 ^ RowSemantics.free xs)).length +
    3 * (encodeNat (a + 2 ^ RowSemantics.free xs)).length

/-- A complete physical list iteration, with no arithmetic or row callback. -/
theorem row_iteration (xs : RowSemantics.Cells) (rest : List Bool) (a : ℕ) :
    RunsExactly computer.step
      (config 0 (Encoding.frame (Dense.CellCodec.encode xs) ++ rest) [] (encodeNat a) [] [] [])
      (config 0 rest [] (encodeNat (a + 2 ^ RowSemantics.free xs)) [] [] []) (rowTime xs a) := by
  have h1 := extract (Dense.CellCodec.encode xs) rest (encodeNat a)
  have h2 := mass_call xs rest (encodeNat a)
  have h3 := addition_call a (2 ^ RowSemantics.free xs) rest
  have h4 := transfer rest (encodeNat (a + 2 ^ RowSemantics.free xs))
  have hr := ((h1.trans h2).trans h3).trans h4
  convert hr using 1 <;> simp only [Dense.CellCodec.encode_length, rowTime] <;> omega

end Counting.Algorithm.KarpLubyRequest.Sampling.TotalMass
