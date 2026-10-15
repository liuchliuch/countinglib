import Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Program
import Counting.Algorithm.KarpLubyRequest.Median.Machine
import Counting.Algorithm.KarpLubyRequest.Output.Machine

/-!
# Actual post-validation evaluator

The prepared payload contains four framed physical fields and a fair-bit tape.
Its group count is copied into a binary countdown. The complete group-body
source is iterated; the resulting physical numerator frames feed the existing
median machine and the selected numerator is moved into the existing rational
normalizer. No count, list, median, or rational evaluator is an instruction.
-/
namespace Counting.Algorithm.KarpLubyRequest.Evaluation
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing FixedFieldMachines
open BinaryCompose

abbrev OuterStack := Iteration.Stack Sampling.GroupBody.machine
abbrev OuterLabel := Iteration.Label Sampling.GroupBody.machine
abbrev OuterState := Iteration.State Sampling.GroupBody.machine
instance outerLabelDecidable : DecidableEq OuterLabel :=
  inferInstanceAs (DecidableEq (Fin 5 ⊕ Sampling.GroupBody.Label))

abbrev Stack := OuterStack ⊕ (Fin 6 ⊕ (Median.Program.Stack ⊕ Output.Program.Stack))
abbrev Memory := OuterState × (Median.Program.State × Output.Program.State)
abbrev State := Option Bool × Memory
def initial : State :=
  (none, (Iteration.machine Sampling.GroupBody.machine).initial,
    Median.Program.computer.initialState, Output.Program.computer.initialState)

set_option backward.isDefEq.respectTransparency false in
inductive Label
  | dispatch | scan : Fin 4 → Label | restore : Fin 4 → Label
  | countMove | countRestore | groupZero
  | emitMove : Fin 3 → Label | emitDelimiter : Fin 3 → Label | emit : Fin 3 → Label
  | groups : OuterLabel → Label
  | resultScan : Fin 4 → Label | resultRestore : Fin 4 → Label
  | groupFinish : GroupOutput.Label → Label
  | medianStart | median : Median.Program.Label → Label
  | numMove | numRestore | denMove | denRestore | outputStart
  | output : Output.Program.Label → Label
  | clearRow | clearMass | done | zero | bad
  deriving DecidableEq, Fintype

def outerStacks : OuterStack ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩
def medianStacks : Median.Program.Stack ↪ Stack :=
  ⟨fun k => .inr (.inr (.inl k)), by intro a b h; exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h))⟩
def outputStacks : Output.Program.Stack ↪ Stack :=
  ⟨fun k => .inr (.inr (.inr k)), by intro a b h; exact Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h))⟩
def extra (i : Fin 6) : Stack := .inr (.inl i)
def random : Stack := outerStacks (Iteration.bodyStack Sampling.GroupBody.machine Sampling.GroupBody.random)
def counter : Stack := outerStacks (Iteration.counter Sampling.GroupBody.machine)
def rows : Stack := extra 0
def mass : Stack := extra 1
def samples : Stack := extra 2
def groups : Stack := extra 3
def reversed : Stack := extra 4
def scratch : Stack := extra 5
def result : Stack := outputStacks Output.Program.computer.k₁

def outerState : (OuterState × (Option Bool × (Median.Program.State × Output.Program.State))) ≃ State where
  toFun v := (v.2.1, v.1, v.2.2)
  invFun v := (v.2.1, v.1, v.2.2)
  left_inv := by rintro ⟨a,b,c⟩; rfl
  right_inv := by rintro ⟨a,b,c⟩; rfl
def medianState : (Median.Program.State × (Option Bool × (OuterState × Output.Program.State))) ≃ State where
  toFun v := (v.2.1, v.2.2.1, v.1, v.2.2.2)
  invFun v := (v.2.2.1, v.1, v.2.1, v.2.2.2)
  left_inv := by rintro ⟨a,b,c,d⟩; rfl
  right_inv := by rintro ⟨a,b,c,d⟩; rfl
def outputState : (Output.Program.State × (Option Bool × (OuterState × Median.Program.State))) ≃ State where
  toFun v := (v.2.1, v.2.2.1, v.2.2.2, v.1)
  invFun v := (v.2.2.2, v.1, v.2.1, v.2.2.1)
  left_inv := by rintro ⟨a,b,c,d⟩; rfl
  right_inv := by rintro ⟨a,b,c,d⟩; rfl

def groupOutputStacks : GroupOutput.Stack ↪ Stack where
  toFun k := ![medianStacks .input, reversed, scratch, groups] k
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;>
    simp_all [medianStacks, reversed, scratch, groups, extra] <;> cases h

def headerField (i : Fin 4) : Stack := extra ⟨i.val, by omega⟩
def headerNext (i : Fin 4) : Label :=
  match i.val with | 0 => .scan 1 | 1 => .scan 2 | 2 => .scan 3 | _ => .countMove
def emitField (i : Fin 3) : Stack := extra ⟨2 - i.val, by omega⟩
def emitNext (i : Fin 3) : Label :=
  match i.val with | 0 => .emitMove 1 | 1 => .emitMove 2 | _ => .groups (Iteration.own Sampling.GroupBody.machine 0)
def returnedField (i : Fin 4) : Stack :=
  match i.val with | 0 => rows | 1 => mass | 2 => samples | _ => reversed
def returnedNext (i : Fin 4) : Label :=
  match i.val with | 0 => .resultScan 1 | 1 => .resultScan 2 | 2 => .resultScan 3 | _ => .groupFinish .reverse

/-- Eight fixed Boolean pushes construct the original literal encoding of zero. -/
def zeroStmt : Stmt Stack Label Memory :=
  .push result (fun _ => true) (.push result (fun _ => false)
    (.push result (fun _ => false) (.push result (fun _ => true)
      (.push result (fun _ => false) (.push result (fun _ => true)
        (.push result (fun _ => true) (.push result (fun _ => true)
          (.load (fun _ => initial) .halt))))))))

def program : Label → Stmt Stack Label Memory
  | .dispatch => .pop random (fun v b => (b,v.2))
      (.branch (fun v => v.1.getD false)
        (.load (fun _ => initial) (.goto (fun _ => .scan 0)))
        (.load (fun _ => initial) (.goto (fun _ => .zero))))
  | .scan i => Frame.scanStmt random scratch (.scan i) (.restore i) .bad
  | .restore i => copyMoveStmt scratch (headerField i) (.restore i) (headerNext i)
  | .countMove => copyMoveStmt groups scratch .countMove .countRestore
  | .countRestore => copyRestoreStmt groups counter scratch .countRestore .groupZero
  | .groupZero => .push random (fun _ => false) (.goto (fun _ => .emitMove 0))
  | .emitMove i => copyMoveStmt (emitField i) scratch (.emitMove i) (.emitDelimiter i)
  | .emitDelimiter i => FrameEmit.delimiterStmt random (.emit i)
  | .emit i => FrameEmit.emitStmt scratch random (.emit i) (emitNext i)
  | .groups l => MachineCall.block outerStacks Label.groups (.resultScan 0) outerState
      (Iteration.program Sampling.GroupBody.machine l)
  | .resultScan i => Frame.scanStmt random scratch (.resultScan i) (.resultRestore i) .bad
  | .resultRestore i => copyMoveStmt scratch (returnedField i) (.resultRestore i) (returnedNext i)
  | .groupFinish l => MachineCall.block groupOutputStacks Label.groupFinish .medianStart
      (MachineCall.unitState Memory) (GroupOutput.program l)
  | .medianStart => .load (fun _ => initial) (.goto (fun _ => .median Median.Program.computer.main))
  | .median l => MachineCall.block medianStacks Label.median .numMove medianState (Median.Program.program l)
  | .numMove => copyMoveStmt (medianStacks .chosen) scratch .numMove .numRestore
  | .numRestore => copyMoveStmt scratch (outputStacks (Output.Program.ex .num)) .numRestore .denMove
  | .denMove => copyMoveStmt samples scratch .denMove .denRestore
  | .denRestore => copyMoveStmt scratch (outputStacks (Output.Program.ex .den)) .denRestore .outputStart
  | .outputStart => .load (fun _ => initial)
      (.goto (fun _ => .output (.inl (RationalArithmetic.Normalization.ph .start))))
  | .output l => MachineCall.block outputStacks Label.output .clearRow outputState (Output.Program.program l)
  | .clearRow => clearStmt rows .clearRow .clearMass
  | .clearMass => clearStmt mass .clearMass .done
  | .done => .load (fun _ => initial) .halt
  | .zero => zeroStmt
  | .bad => .load (fun _ => initial) .halt

instance stateFinite : Fintype State := by
  letI : Fintype OuterState := (Iteration.computer Sampling.GroupBody.machine).σFin
  letI : Fintype Median.Program.State := Median.Program.computer.σFin
  letI : Fintype Output.Program.State := Output.Program.computer.σFin
  exact inferInstanceAs (Fintype (Option Bool × (OuterState × (Median.Program.State × Output.Program.State))))

def machine : Machine where
  K := Stack
  input := random
  output := result
  Label := Label
  main := .dispatch
  State := State
  initial := initial
  program := program

abbrev computer := machine.computer

end Counting.Algorithm.KarpLubyRequest.Evaluation
