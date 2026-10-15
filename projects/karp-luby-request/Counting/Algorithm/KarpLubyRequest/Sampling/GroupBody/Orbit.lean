import Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Cost

/-! # Outer group iteration and the original occurrence order -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
open Counting.Algorithm.KarpLuby
open Counting.Algorithm.KarpLubyMachine
open TapeIterationSpec

theorem step_view {n : ℕ} (cs : List (DNF.Clause n)) (samples width : ℕ)
    (xs : List ℕ) (tape : List Bool) :
    step cs samples width (GroupOutput.reversed xs, tape) =
      (GroupOutput.reversed (groupStep cs samples width (xs, tape)).1,
        (groupStep cs samples width (xs, tape)).2) := by
  dsimp only [step, groupStep]
  rw [GroupOutput.reversed_append]

theorem iterate_view {n : ℕ} (cs : List (DNF.Clause n)) (samples width groups : ℕ)
    (xs : List ℕ) (tape : List Bool) :
    (step cs samples width)^[groups] (GroupOutput.reversed xs, tape) =
      (GroupOutput.reversed ((groupStep cs samples width)^[groups] (xs, tape)).1,
        ((groupStep cs samples width)^[groups] (xs, tape)).2) := by
  induction groups generalizing xs tape with
  | zero => rfl
  | succ groups ih =>
    rw [Function.iterate_succ_apply, step_view, ih, Function.iterate_succ_apply]

/-- Each outer body receives the full physical random block needed by all its
inner samples. No body call is assumed on an insufficient random suffix. -/
theorem source_on (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (samples groups : ℕ)
    (xs : List ℕ) (tape : List Bool)
    (havailable : groups * (samples * (encodeNat (TotalMass.rowSum rows)).length) ≤ tape.length)
    (j : ℕ) (hj : j < groups) :
    let e := stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)) (encodeNat samples)
    let f := step (rows.map (DenseNormalization.denote n)) samples (encodeNat (TotalMass.rowSum rows)).length
    Iteration.SourceRun machine (e.encode (f^[j] (GroupOutput.reversed xs, tape)))
      (e.encode (f (f^[j] (GroupOutput.reversed xs, tape))))
      (sourceTime n rows samples (f^[j] (GroupOutput.reversed xs, tape))) := by
  dsimp only
  apply source_run n rows hlen
  rw [iterate_view]
  exact TapeBounds.group_tape_available _ samples groups _ j xs tape hj havailable

/-- The second application of the same real repeat compiler performs all
groups and stores their numerators in the original logical order. -/
theorem group_loop (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (samples groups : ℕ)
    (xs : List ℕ) (tape : List Bool)
    (havailable : groups * (samples * (encodeNat (TotalMass.rowSum rows)).length) ≤ tape.length) :
    let e := stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)) (encodeNat samples)
    let f := step (rows.map (DenseNormalization.denote n)) samples (encodeNat (TotalMass.rowSum rows)).length
    let original := (groupStep (rows.map (DenseNormalization.denote n)) samples
      (encodeNat (TotalMass.rowSum rows)).length)^[groups] (xs, tape)
    RunsExactly (Iteration.computer machine).step
      (cfg (Iteration.own machine 0) machine.initial
        (Iteration.ready machine (encodeNat groups) (e.encode (GroupOutput.reversed xs, tape))))
      (Iteration.finished machine (e.encode (GroupOutput.reversed original.1, original.2)))
      (Iteration.ticks e f (sourceTime n rows samples) groups (GroupOutput.reversed xs, tape)) := by
  dsimp only
  have h := Iteration.run_on machine
    (stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)) (encodeNat samples))
    (step (rows.map (DenseNormalization.denote n)) samples (encodeNat (TotalMass.rowSum rows)).length)
    (sourceTime n rows samples) groups (GroupOutput.reversed xs, tape)
    (source_on n rows hlen samples groups xs tape havailable)
  rw [iterate_view] at h
  exact h

end Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
