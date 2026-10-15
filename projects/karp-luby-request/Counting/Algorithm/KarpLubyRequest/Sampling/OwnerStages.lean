import Counting.Algorithm.KarpLubyRequest.Sampling.OwnerProgram

/-! # Physical extraction, assignment copying and row calls for ownership -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Owner
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby

private theorem as_frame (history row assignment scratch : List Bool) :
    tapes history row assignment [] scratch =
      tapes3 (tapes [] [] assignment [] []) (0 : Stack) 1 4 history row scratch := by
  funext k; fin_cases k <;> rfl

theorem empty_step (assignment : List Bool) :
    computer.step (config 0 [] [] assignment [] []) = some (finished true [] assignment) := by
  simp [FinTM2.step, TM2.step, program, loop, config, finished, cfg, TM2.stepAux, tapes]
  rfl

theorem nonempty_step (bit : Bool) (rest assignment : List Bool) :
    computer.step (config 0 (bit :: rest) [] assignment [] []) =
      some (config 1 (bit :: rest) [] assignment [] []) := by
  simp [FinTM2.step, TM2.step, program, loop, config, cfg, TM2.stepAux, tapes]
  rfl

theorem extract (word rest assignment : List Bool) :
    RunsExactly computer.step (config 0 (Encoding.frame word ++ rest) [] assignment [] [])
      (config 3 rest word assignment [] []) (2 * word.length + 3) := by
  have hc : computer.step (config 0 (Encoding.frame word ++ rest) [] assignment [] []) =
      some (config 1 (Encoding.frame word ++ rest) [] assignment [] []) := by
    cases word with
    | nil => exact nonempty_step false rest assignment
    | cons bit word => exact nonempty_step true (bit :: (Encoding.frame word ++ rest)) assignment
  have hs : ExecutesAt computer.step (1 : Label) (Frame.scanStmt (0 : Stack) 4 1 2 0) := by
    intro state tape; rfl
  have hm : ExecutesAt computer.step (2 : Label) (copyMoveStmt (4 : Stack) 1 2 3) := by
    intro state tape; rfl
  have he : RunsExactly computer.step (config 1 (Encoding.frame word ++ rest) [] assignment [] [])
      (config 3 rest word assignment [] []) (2 * (word.length + 1)) := by
    simpa only [config, ← as_frame, ← Contract.frame_eq, List.append_nil] using
      Frame.extract_exact (0 : Stack) 1 4 (by decide) (by decide) (by decide)
        computer.step (1 : Label) 2 3 0 hs hm (false, true)
        (tapes [] [] assignment [] []) word rest []
  convert (runsExactly_one hc).trans he using 1 <;> omega

theorem copy_assignment (history row assignment : List Bool) :
    RunsExactly computer.step (config 3 history row assignment [] [])
      (config 5 history row assignment assignment []) (2 * assignment.length + 2) := by
  have hm : ExecutesAt computer.step (3 : Label) (copyMoveStmt (2 : Stack) 4 3 4) := by
    intro state tape; rfl
  have hr : ExecutesAt computer.step (4 : Label) (copyRestoreStmt (2 : Stack) 3 4 4 5) := by
    intro state tape; rfl
  have he : Function.update (tapes history row assignment [] []) (3 : Stack) assignment =
      tapes history row assignment assignment [] := by funext k; fin_cases k <;> rfl
  have h := Embedded.copy_into (2 : Stack) 3 4 (by decide) (by decide) (by decide)
    computer.step (3 : Label) 4 5 hm hr (false, true) (tapes history row assignment [] []) rfl rfl
  change RunsExactly computer.step _ (cfg 5 (false, true)
    (Function.update (tapes history row assignment [] []) 3 assignment)) (2 * assignment.length + 2) at h
  rw [he] at h
  exact h

theorem evaluate (xs : RowSemantics.Cells) (history assignment : List Bool)
    (hlen : assignment.length = xs.length) :
    RunsExactly computer.step (config 5 history (Dense.CellCodec.encode xs) assignment assignment [])
      (config 6 history [] assignment [] [] (RowEval.value xs assignment)) (xs.length + 1) := by
  have source := RowEval.scan_exact xs assignment true
  have hd : assignment.drop xs.length = [] := List.drop_eq_nil_of_le (by omega)
  rw [hd, Bool.true_and] at source
  have ha : Embedded.Rel rowStacks rowLabel 6 (tapes history [] assignment [] [])
      (RowEval.config (Dense.CellCodec.encode xs) assignment true)
      (config 5 history (Dense.CellCodec.encode xs) assignment assignment []) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro k hk; fin_cases k <;>
        first | rfl | exact False.elim (hk 0 rfl) | exact False.elim (hk 1 rfl)
  have hz : Embedded.Rel rowStacks rowLabel 6 (tapes history [] assignment [] [])
      (RowEval.finished [] [] (RowEval.value xs assignment))
      (config 6 history [] assignment [] [] (RowEval.value xs assignment)) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro k hk; fin_cases k <;>
        first | rfl | exact False.elim (hk 0 rfl) | exact False.elim (hk 1 rfl)
  obtain ⟨ending, hr, he⟩ := Embedded.run rowStacks rowLabel 6 RowEval.program program row_code
    _ _ _ (tapes history [] assignment [] []) (xs.length + 1) ha source
  rw [MachineCall.rel_unique rowStacks rowLabel 6 _ _ _ _ he hz] at hr
  exact hr

theorem reject_step (history assignment : List Bool) :
    computer.step (config 6 history [] assignment [] [] true) =
      some (finished false history assignment) := by
  simp [FinTM2.step, TM2.step, program, tested, config, finished, cfg, TM2.stepAux]
  rfl

theorem continue_step (history assignment : List Bool) :
    computer.step (config 6 history [] assignment [] [] false) =
      some (config 0 history [] assignment [] []) := by
  simp [FinTM2.step, TM2.step, program, tested, config, cfg, TM2.stepAux]
  rfl

theorem test_row (xs : RowSemantics.Cells) (history assignment : List Bool)
    (hlen : assignment.length = xs.length) :
    RunsExactly computer.step
      (config 0 (Encoding.frame (Dense.CellCodec.encode xs) ++ history) [] assignment [] [])
      (config 6 history [] assignment [] [] (RowEval.value xs assignment))
      (5 * xs.length + 2 * assignment.length + 6) := by
  have h := ((extract (Dense.CellCodec.encode xs) history assignment).trans
    (copy_assignment history (Dense.CellCodec.encode xs) assignment)).trans
      (evaluate xs history assignment hlen)
  convert h using 1 <;> simp only [Dense.CellCodec.encode_length] <;> omega

end Counting.Algorithm.KarpLubyRequest.Sampling.Owner
