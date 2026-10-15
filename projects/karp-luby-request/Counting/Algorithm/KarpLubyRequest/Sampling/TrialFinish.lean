import Counting.Algorithm.KarpLubyRequest.Sampling.TrialBank

/-! # Real dyadic-output construction and finite cleanup -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Trial
open Turing Computability Holant.Complexity StackProtocol

def cleanupTime (d : Data) : ℕ :=
  d.rank.length + d.remaining.length + d.row.length + d.rowMass.length + d.history.length + d.clock.length + d.left.length + d.right.length + d.work.length + d.arithmeticOutput.length + d.scratch.length + d.massRow.length + d.assignment.length + d.assignmentCopy.length + 15

set_option maxHeartbeats 1200000 in
/-- Fourteen actual clear loops, followed by the actual halting instruction. -/
theorem cleanup_exact (d : Data) :
    RunsExactly computer.step (configuration (.clear 0) initial d)
      (finalConfiguration d.rows d.mass d.random d.output) (cleanupTime d) := by
  let b0 := d.tapes
  let b1 := Function.update b0 (clearStack 0) []
  have h0 := clear_exact computer.step (clearStack 0) (.clear 0) (clearNext 0)
    (by intro state tape; rfl) initial.2 b0
  let b2 := Function.update b1 (clearStack 1) []
  have h1 := clear_exact computer.step (clearStack 1) (.clear 1) (clearNext 1)
    (by intro state tape; rfl) initial.2 b1
  let b3 := Function.update b2 (clearStack 2) []
  have h2 := clear_exact computer.step (clearStack 2) (.clear 2) (clearNext 2)
    (by intro state tape; rfl) initial.2 b2
  let b4 := Function.update b3 (clearStack 3) []
  have h3 := clear_exact computer.step (clearStack 3) (.clear 3) (clearNext 3)
    (by intro state tape; rfl) initial.2 b3
  let b5 := Function.update b4 (clearStack 4) []
  have h4 := clear_exact computer.step (clearStack 4) (.clear 4) (clearNext 4)
    (by intro state tape; rfl) initial.2 b4
  let b6 := Function.update b5 (clearStack 5) []
  have h5 := clear_exact computer.step (clearStack 5) (.clear 5) (clearNext 5)
    (by intro state tape; rfl) initial.2 b5
  let b7 := Function.update b6 (clearStack 6) []
  have h6 := clear_exact computer.step (clearStack 6) (.clear 6) (clearNext 6)
    (by intro state tape; rfl) initial.2 b6
  let b8 := Function.update b7 (clearStack 7) []
  have h7 := clear_exact computer.step (clearStack 7) (.clear 7) (clearNext 7)
    (by intro state tape; rfl) initial.2 b7
  let b9 := Function.update b8 (clearStack 8) []
  have h8 := clear_exact computer.step (clearStack 8) (.clear 8) (clearNext 8)
    (by intro state tape; rfl) initial.2 b8
  let b10 := Function.update b9 (clearStack 9) []
  have h9 := clear_exact computer.step (clearStack 9) (.clear 9) (clearNext 9)
    (by intro state tape; rfl) initial.2 b9
  let b11 := Function.update b10 (clearStack 10) []
  have h10 := clear_exact computer.step (clearStack 10) (.clear 10) (clearNext 10)
    (by intro state tape; rfl) initial.2 b10
  let b12 := Function.update b11 (clearStack 11) []
  have h11 := clear_exact computer.step (clearStack 11) (.clear 11) (clearNext 11)
    (by intro state tape; rfl) initial.2 b11
  let b13 := Function.update b12 (clearStack 12) []
  have h12 := clear_exact computer.step (clearStack 12) (.clear 12) (clearNext 12)
    (by intro state tape; rfl) initial.2 b12
  let b14 := Function.update b13 (clearStack 13) []
  have h13 := clear_exact computer.step (clearStack 13) (.clear 13) (clearNext 13)
    (by intro state tape; rfl) initial.2 b13
  have he : computer.step (cfg .done initial.2 b14) =
      some (finalConfiguration d.rows d.mass d.random d.output) := by
    change some (⟨none, initial, b14⟩ : computer.Cfg) = _
    congr 2
    funext k
    cases k <;> rfl
  have hr := (((((((((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).trans h9).trans h10).trans h11).trans h12).trans h13) 
  have hf := hr.trans (runsExactly_one he)
  have ht : 1 + (((b13 (clearStack 13)).length + 1) + (((b12 (clearStack 12)).length + 1) + (((b11 (clearStack 11)).length + 1) + (((b10 (clearStack 10)).length + 1) + (((b9 (clearStack 9)).length + 1) + (((b8 (clearStack 8)).length + 1) + (((b7 (clearStack 7)).length + 1) + (((b6 (clearStack 6)).length + 1) + (((b5 (clearStack 5)).length + 1) + (((b4 (clearStack 4)).length + 1) + (((b3 (clearStack 3)).length + 1) + (((b2 (clearStack 2)).length + 1) + (((b1 (clearStack 1)).length + 1) + ((b0 (clearStack 0)).length + 1)))))))))))))) = cleanupTime d := by
    simp [cleanupTime, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13,
      clearStack, Data.tapes]
    omega
  rw [ht] at hf
  exact hf

theorem scale_step_cons (d : Data) (bit : Bool) (word output : List Bool) :
    computer.step (configuration .scale initial {d with clock := bit :: word, output := output}) =
      some (configuration .scale initial {d with clock := word, output := false :: output}) := by
  simp [FinTM2.step, TM2.step, program, scaleLoop, configuration, initial, Data.tapes, TM2.stepAux]
  congr 2
  funext k
  cases k <;> rfl

theorem scale_step_nil (d : Data) (output : List Bool) :
    computer.step (configuration .scale initial {d with clock := [], output := output}) =
      some (configuration (.clear 0) initial {d with clock := [], output := output}) := by
  simp [FinTM2.step, TM2.step, program, scaleLoop, configuration, initial, Data.tapes, TM2.stepAux]
  congr 2
  funext k
  cases k <;> rfl

theorem scale_exact (d : Data) (word output : List Bool) :
    RunsExactly computer.step
      (configuration .scale initial {d with clock := word, output := output})
      (configuration (.clear 0) initial
        {d with clock := [], output := List.replicate word.length false ++ output})
      (word.length + 1) := by
  induction word generalizing output with
  | nil => exact runsExactly_one (scale_step_nil d output)
  | cons bit word ih =>
    have hr := (runsExactly_one (scale_step_cons d bit word output)).trans (ih (false :: output))
    convert hr using 1
    · congr 2
      simp only [List.length_cons, List.replicate_succ', List.append_assoc, List.singleton_append]

theorem scale_copy (d : Data) (hc : d.clock = []) (hs : d.scratch = []) :
    RunsExactly computer.step (configuration .scaleMove initial d)
      (configuration .scaleStart initial {d with clock := d.mass}) (2 * d.mass.length + 2) := by
  have hm : ExecutesAt computer.step .scaleMove
      (copyMoveStmt .mass .scratch .scaleMove .scaleRestore) := by intro state tape; rfl
  have hr : ExecutesAt computer.step .scaleRestore
      (copyRestoreStmt .mass .clock .scratch .scaleRestore .scaleStart) := by intro state tape; rfl
  have h := Embedded.copy_into Stack.mass Stack.clock Stack.scratch (by decide) (by decide)
    (by decide) computer.step .scaleMove .scaleRestore .scaleStart hm hr initial.2 d.tapes hc hs
  have hb : Function.update d.tapes Stack.clock (d.tapes .mass) =
      ({d with clock := d.mass} : Data).tapes := by
    funext k; cases k <;> rfl
  rw [hb] at h
  exact h

theorem scale_start (d : Data) (ho : d.output = []) :
    computer.step (configuration .scaleStart initial d) =
      some (configuration .scale initial {d with output := [true]}) := by
  simp [FinTM2.step, TM2.step, program, configuration, initial, Data.tapes, TM2.stepAux, ho]
  congr 2
  funext k
  cases k <;> rfl

/-- The output's exponential numeric value costs only its physically constructed
binary width. The mass-word copy and every scan transition are included. -/
theorem scale_output (d : Data) (hc : d.clock = []) (hs : d.scratch = []) (ho : d.output = []) :
    RunsExactly computer.step (configuration .scaleMove initial d)
      (configuration (.clear 0) initial {d with clock := [], output := encodeNat (2 ^ d.mass.length)})
      (3 * d.mass.length + 4) := by
  have h1 := scale_copy d hc hs
  have h2 := runsExactly_one (scale_start {d with clock := d.mass} ho)
  have h3 := scale_exact d d.mass [true]
  rw [RowMass.power_word] at h3
  convert (h1.trans h2).trans h3 using 1 <;> omega

end Counting.Algorithm.KarpLubyRequest.Sampling.Trial

