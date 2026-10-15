import Counting.Algorithm.KarpLubyRequest.Evaluation.Return
import Counting.Algorithm.KarpLubyRequest.Evaluation.Finish
import Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Orbit

/-! Both materialized loops execute in the evaluator and return actual frames. -/
namespace Counting.Algorithm.KarpLubyRequest.Evaluation
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine
open Sampling
set_option backward.isDefEq.respectTransparency false

def groupResult (n : ℕ) (rows : List RowSemantics.Cells) (s g : ℕ) (tape : List Bool) :
    List ℕ × List Bool :=
  (TapeIterationSpec.groupStep (rows.map (DenseNormalization.denote n)) s
    (encodeNat (TotalMass.rowSum rows)).length)^[g] ([], tape)

def outerTime (n : ℕ) (rows : List RowSemantics.Cells) (s g : ℕ) (tape : List Bool) : ℕ :=
  Iteration.ticks
    (GroupBody.stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)) (encodeNat s))
    (GroupBody.step (rows.map (DenseNormalization.denote n)) s (encodeNat (TotalMass.rowSum rows)).length)
    (GroupBody.sourceTime n rows s) g (GroupOutput.reversed [], tape)

theorem result_length (n : ℕ) (rows : List RowSemantics.Cells) (s g : ℕ) (tape : List Bool) :
    (groupResult n rows s g tape).1.length = g := by
  exact (TapeBounds.group_prefix_length _ s _ g [] tape).trans (Nat.zero_add g)

theorem result_suffix (n : ℕ) (rows : List RowSemantics.Cells) (s g : ℕ) (tape : List Bool)
    (hlen : tape.length = g*(s*(encodeNat (TotalMass.rowSum rows)).length)) :
    (groupResult n rows s g tape).2 = [] := by
  dsimp only [groupResult]
  rw [TapeIterationSpec.group_iterate_raw]
  change tape.drop (g*(s*(encodeNat (TotalMass.rowSum rows)).length)) = []
  rw [← hlen, List.drop_length]

theorem outer_empty : Iteration.ready GroupBody.machine [] [] = fun _ => [] := by
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k =>
    change wordTape GroupBody.random [] k = []
    simp only [wordTape, Function.update_apply, ite_self]

/-- The complete nested source call follows the physically stored group
counter. The returned order and suffix are those of the original group step. -/
theorem run_groups (n : ℕ) (rows : List RowSemantics.Cells)
    (hrows : ∀ row ∈ rows, row.length = n) (s g : ℕ) (tape : List Bool)
    (hlen : tape.length = g*(s*(encodeNat (TotalMass.rowSum rows)).length)) :
    RunsExactly computer.step
      (configuration (.groups (Iteration.own GroupBody.machine 0)) initial
        (frontData (encodeNat g)
          (GroupBody.word (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)) (encodeNat s) [] tape)
          (fieldWords [] [] [] (encodeNat g) [] [])))
      (configuration (.resultScan 0) initial
        (frontData []
          (GroupBody.word (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)) (encodeNat s)
            (GroupOutput.reversed (groupResult n rows s g tape).1) [])
          (fieldWords [] [] [] (encodeNat g) [] [])))
      (outerTime n rows s g tape) := by
  have source := GroupBody.group_loop n rows hrows s g [] tape (by omega)
  have run := outer_call ({fields := fieldWords [] [] [] (encodeNat g) [] []} : Data)
    (none, Median.Program.computer.initialState, Output.Program.computer.initialState)
    (Iteration.own GroupBody.machine 0) _ _ _ _ _ source
  have hs := result_suffix n rows s g tape hlen
  change RunsExactly computer.step _
    (configuration (.resultScan 0) initial
      (frontData [] (GroupBody.word (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
        (encodeNat s) (GroupOutput.reversed (groupResult n rows s g tape).1)
        (groupResult n rows s g tape).2) (fieldWords [] [] [] (encodeNat g) [] [])))
    (outerTime n rows s g tape) at run
  rw [hs] at run
  exact run

def groupPhaseTime (n : ℕ) (rows : List RowSemantics.Cells) (s g : ℕ) (tape : List Bool) : ℕ :=
  let r := Dense.CellCodec.rows rows
  let m := encodeNat (TotalMass.rowSum rows)
  (4*(r.length+m.length+(encodeNat s).length+(encodeNat g).length)+21) +
    outerTime n rows s g tape +
    (2*(r.length+m.length+(encodeNat s).length+
      (GroupOutput.reversed (groupResult n rows s g tape).1).length)+8)

/-- Tag parsing, four field extractions, numeric countdown, both nested loops,
and four result extractions form one actual source execution. -/
theorem group_phase (n : ℕ) (rows : List RowSemantics.Cells)
    (hrows : ∀ row ∈ rows, row.length = n) (s g : ℕ) (tape : List Bool)
    (hlen : tape.length = g*(s*(encodeNat (TotalMass.rowSum rows)).length)) :
    RunsExactly computer.step
      (initList computer (payload (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
        (encodeNat s) (encodeNat g) tape))
      (configuration (.groupFinish .reverse) initial
        (groupInputData (fun _ => []) (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
          (encodeNat s) (groupResult n rows s g tape).1))
      (groupPhaseTime n rows s g tape) := by
  have h0 := prepare_payload (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
    (encodeNat s) (encodeNat g) tape
  have h1 := run_groups n rows hrows s g tape hlen
  have h2 := parse_results (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
    (encodeNat s) (encodeNat g) (GroupOutput.reversed (groupResult n rows s g tape).1) []
  have hd : frontData [] [] (fieldWords (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
      (encodeNat s) (encodeNat g) (GroupOutput.reversed (groupResult n rows s g tape).1) []) =
      groupInputData (fun _ => []) (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
        (encodeNat s) (groupResult n rows s g tape).1 := by
    dsimp only [frontData, groupInputData]
    rw [outer_empty, result_length]
  rw [hd] at h2
  have h := (h0.trans h1).trans h2
  dsimp only [FinTM2.step] at h ⊢
  simpa only [groupPhaseTime, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end Counting.Algorithm.KarpLubyRequest.Evaluation
