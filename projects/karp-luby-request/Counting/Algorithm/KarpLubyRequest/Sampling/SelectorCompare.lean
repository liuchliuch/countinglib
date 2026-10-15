import Counting.Algorithm.KarpLubyRequest.Sampling.SelectorProgram

/-! # The actual selector's extraction, retained copies and interval comparison -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Selector
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby

private theorem as_frame (source rank row scratch history : List Bool) :
    tapes source rank row [] [] [] scratch [] [] history [] =
      tapes3 (tapes [] rank [] [] [] [] [] [] [] history []) (0 : Stack) 2 6 source row scratch := by
  funext k; fin_cases k <;> rfl

theorem loop_nonempty (bit : Bool) (rest rank history : List Bool) :
    computer.step (config 0 (bit :: rest) rank [] [] [] [] [] [] [] history []) =
      some (config 1 (bit :: rest) rank [] [] [] [] [] [] [] history []) := by
  simp [FinTM2.step, TM2.step, program, loop, config, cfg, TM2.stepAux, tapes]
  rfl

theorem extract (row rest rank history : List Bool) :
    RunsExactly computer.step
      (config 0 (Encoding.frame row ++ rest) rank [] [] [] [] [] [] [] history [])
      (config 3 rest rank row [] [] [] [] [] [] history []) (2 * row.length + 3) := by
  have hc : computer.step (config 0 (Encoding.frame row ++ rest) rank [] [] [] [] [] [] [] history []) =
      some (config 1 (Encoding.frame row ++ rest) rank [] [] [] [] [] [] [] history []) := by
    cases row with
    | nil => exact loop_nonempty false rest rank history
    | cons bit word => exact loop_nonempty true (bit :: (Encoding.frame word ++ rest)) rank history
  have hs : ExecutesAt computer.step (1 : Label) (Frame.scanStmt (0 : Stack) 6 1 2 0) := by
    intro state tape; rfl
  have hr : ExecutesAt computer.step (2 : Label) (copyMoveStmt (6 : Stack) 2 2 3) := by
    intro state tape; rfl
  have he : RunsExactly computer.step
      (config 1 (Encoding.frame row ++ rest) rank [] [] [] [] [] [] [] history [])
      (config 3 rest rank row [] [] [] [] [] [] history []) (2 * (row.length + 1)) := by
    simpa only [config, ← as_frame, ← Contract.frame_eq, List.append_nil] using
      Frame.extract_exact (0 : Stack) 2 6 (by decide) (by decide) (by decide)
        computer.step (1 : Label) 2 3 0 hs hr BinaryArithmetic.Addition.initial
        (tapes [] rank [] [] [] [] [] [] [] history []) row rest []
  convert (runsExactly_one hc).trans he using 1 <;> omega

theorem copy_row (rest rank row history : List Bool) :
    RunsExactly computer.step (config 3 rest rank row [] [] [] [] [] [] history [])
      (config 5 rest rank row [] [] [] [] [] [] history row) (2 * row.length + 2) := by
  have hm : ExecutesAt computer.step (3 : Label) (copyMoveStmt (2 : Stack) 6 3 4) := by
    intro state tape; rfl
  have hr : ExecutesAt computer.step (4 : Label) (copyRestoreStmt (2 : Stack) 10 6 4 5) := by
    intro state tape; rfl
  have he : Function.update (tapes rest rank row [] [] [] [] [] [] history []) (10 : Stack) row =
      tapes rest rank row [] [] [] [] [] [] history row := by funext k; fin_cases k <;> rfl
  have h := Embedded.copy_into (2 : Stack) 10 6 (by decide) (by decide) (by decide)
    computer.step (3 : Label) 4 5 hm hr BinaryArithmetic.Addition.initial
    (tapes rest rank row [] [] [] [] [] [] history []) rfl rfl
  change RunsExactly computer.step _
    (cfg 5 BinaryArithmetic.Addition.initial
      (Function.update (tapes rest rank row [] [] [] [] [] [] history []) 10 row)) (2 * row.length + 2) at h
  rw [he] at h
  exact h

private theorem mass_frame (rest rank row mass history massRow : List Bool) :
    ∀ k : Fin 11, k ≠ 3 → k ≠ 10 →
    tapes rest rank row mass [] [] [] [] [] history massRow k =
      tapes rest rank row [] [] [] [] [] [] history [] k := by
  intro k h3 h10
  rcases k with ⟨k, hk⟩
  interval_cases k <;> simp_all [tapes]


#check mass_frame

set_option backward.isDefEq.respectTransparency false in
theorem mass_call (xs : RowSemantics.Cells) (rest rank history : List Bool) :
    RunsExactly computer.step
      (config 5 rest rank (Dense.CellCodec.encode xs) [] [] [] [] [] [] history (Dense.CellCodec.encode xs))
      (config 8 rest rank (Dense.CellCodec.encode xs) (encodeNat (2 ^ RowSemantics.free xs))
        [] [] [] [] [] history []) (xs.length + 3) := by
  apply MachineCall.run massStacks massLabel 8 massState RowMass.program program mass_code
    BinaryArithmetic.Addition.initial (tapes rest rank (Dense.CellCodec.encode xs) [] [] [] [] [] [] history [])
    (RowMass.config 0 (Dense.CellCodec.encode xs) [])
    (⟨none, (none, ()), RowMass.tapes [] (encodeNat (2 ^ RowSemantics.free xs))⟩)
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · rfl
      · have hi : i = 0 := Fin.eq_zero i
        subst i
        rfl
    · intro k hk
      exact mass_frame rest rank (Dense.CellCodec.encode xs) [] history
        (Dense.CellCodec.encode xs) k (hk 1) (hk 0)
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · rfl
      · have hi : i = 0 := Fin.eq_zero i
        subst i
        rfl
    · intro k hk
      exact mass_frame rest rank (Dense.CellCodec.encode xs)
        (encodeNat (2 ^ RowSemantics.free xs)) history [] k (hk 1) (hk 0)
  · exact RowMass.halt_exact xs

theorem copy_rank (rest rank row mass history : List Bool) :
    RunsExactly computer.step (config 8 rest rank row mass [] [] [] [] [] history [])
      (config 10 rest rank row mass rank [] [] [] [] history []) (2 * rank.length + 2) := by
  have hm : ExecutesAt computer.step (8 : Label) (copyMoveStmt (1 : Stack) 6 8 9) := by
    intro state tape; rfl
  have hr : ExecutesAt computer.step (9 : Label) (copyRestoreStmt (1 : Stack) 4 6 9 10) := by
    intro state tape; rfl
  have he : Function.update (tapes rest rank row mass [] [] [] [] [] history []) (4 : Stack) rank =
      tapes rest rank row mass rank [] [] [] [] history [] := by funext k; fin_cases k <;> rfl
  have h := Embedded.copy_into (1 : Stack) 4 6 (by decide) (by decide) (by decide)
    computer.step (8 : Label) 9 10 hm hr BinaryArithmetic.Addition.initial
    (tapes rest rank row mass [] [] [] [] [] history []) rfl rfl
  change RunsExactly computer.step _
    (cfg 10 BinaryArithmetic.Addition.initial
      (Function.update (tapes rest rank row mass [] [] [] [] [] history []) 4 rank)) (2 * rank.length + 2) at h
  rw [he] at h
  exact h

theorem copy_mass (rest rank row mass history : List Bool) :
    RunsExactly computer.step (config 10 rest rank row mass rank [] [] [] [] history [])
      (config 12 rest rank row mass rank mass [] [] [] history []) (2 * mass.length + 2) := by
  have hm : ExecutesAt computer.step (10 : Label) (copyMoveStmt (3 : Stack) 6 10 11) := by
    intro state tape; rfl
  have hr : ExecutesAt computer.step (11 : Label) (copyRestoreStmt (3 : Stack) 5 6 11 12) := by
    intro state tape; rfl
  have he : Function.update (tapes rest rank row mass rank [] [] [] [] history []) (5 : Stack) mass =
      tapes rest rank row mass rank mass [] [] [] history [] := by funext k; fin_cases k <;> rfl
  have h := Embedded.copy_into (3 : Stack) 5 6 (by decide) (by decide) (by decide)
    computer.step (10 : Label) 11 12 hm hr BinaryArithmetic.Addition.initial
    (tapes rest rank row mass rank [] [] [] [] history []) rfl rfl
  change RunsExactly computer.step _
    (cfg 12 BinaryArithmetic.Addition.initial
      (Function.update (tapes rest rank row mass rank [] [] [] [] history []) 5 mass)) (2 * mass.length + 2) at h
  rw [he] at h
  exact h

theorem comparison (r m : ℕ) (rest row history : List Bool) :
    RunsExactly computer.step
      (config 12 rest (encodeNat r) row (encodeNat m) (encodeNat r) (encodeNat m) [] [] [] history [])
      (config 13 rest (encodeNat r) row (encodeNat m) [] [] [] [] [decide (r < m)] history [])
      (max (encodeNat r).length (encodeNat m).length + 1) := by
  apply MachineCall.run compareStacks compareLabel 13 arithmeticState BinaryArithmetic.Comparison.program
    program comparison_code none (tapes rest (encodeNat r) row (encodeNat m) [] [] [] [] [] history [])
    (BinaryArithmetic.Comparison.cfg (some ()) false (encodeNat r) (encodeNat m) [])
    (BinaryArithmetic.Comparison.cfg none false [] [] [decide (r < m)])
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
  · exact BinaryArithmetic.Comparison.compute_encodeNat_exact r m

def compareTime (xs : RowSemantics.Cells) (r : ℕ) : ℕ :=
  9 * xs.length + 13 + 2 * (encodeNat r).length +
    2 * (encodeNat (2 ^ RowSemantics.free xs)).length +
    max (encodeNat r).length (encodeNat (2 ^ RowSemantics.free xs)).length

/-- Every copy and operand construction is included before the actual test. -/
theorem compare_row (xs : RowSemantics.Cells) (r : ℕ) (rest history : List Bool) :
    RunsExactly computer.step
      (config 0 (Encoding.frame (Dense.CellCodec.encode xs) ++ rest) (encodeNat r)
        [] [] [] [] [] [] [] history [])
      (config 13 rest (encodeNat r) (Dense.CellCodec.encode xs) (encodeNat (2 ^ RowSemantics.free xs))
        [] [] [] [] [decide (r < 2 ^ RowSemantics.free xs)] history []) (compareTime xs r) := by
  have h1 := extract (Dense.CellCodec.encode xs) rest (encodeNat r) history
  have h2 := copy_row rest (encodeNat r) (Dense.CellCodec.encode xs) history
  have h3 := mass_call xs rest (encodeNat r) history
  have h4 := copy_rank rest (encodeNat r) (Dense.CellCodec.encode xs) (encodeNat (2 ^ RowSemantics.free xs)) history
  have h5 := copy_mass rest (encodeNat r) (Dense.CellCodec.encode xs) (encodeNat (2 ^ RowSemantics.free xs)) history
  have h6 := comparison r (2 ^ RowSemantics.free xs) rest (Dense.CellCodec.encode xs) history
  have hr := ((((h1.trans h2).trans h3).trans h4).trans h5).trans h6
  convert hr using 1 <;> simp only [compareTime, Dense.CellCodec.encode_length] <;> omega

end Counting.Algorithm.KarpLubyRequest.Sampling.Selector
