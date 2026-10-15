import Counting.Algorithm.KarpLubyRequest.Iteration.Orbit
import Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody.Program
import Counting.Algorithm.KarpLubyRequest.GroupOutput.Run

/-!
# A real group body with a physically stored sample count

Four frame scans extract rows, mass, sample count and the reversed numerator
history. The sample count is copied into the real repeat compiler's countdown.
Two frame emitters and the empty-accumulator delimiter build its input; after
the complete nested execution, three scans recover its rows, mass and result.
The canonical GroupOutput append program records that result, then four frame
emitters rebuild the outer state on the remaining random tape. Group count is
absent from this finite program: an outer repeat compiler supplies that count.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open FixedFieldMachines BinaryCompose

abbrev InnerStack := Iteration.Stack SampleBody.machine
abbrev InnerLabel := Iteration.Label SampleBody.machine
instance innerLabelDecidable : DecidableEq InnerLabel :=
  inferInstanceAs (DecidableEq (Fin 5 ⊕ SampleBody.Label))
abbrev Stack := InnerStack ⊕ Fin 6
abbrev Memory := SampleBody.State
abbrev State := Option Bool × Memory
def initial : State := (none, SampleBody.machine.initial)

set_option backward.isDefEq.respectTransparency false in
inductive Label
  | scan : Fin 4 → Label
  | restore : Fin 4 → Label
  | countMove | countRestore | innerZero
  | innerMove : Fin 2 → Label
  | innerDelimiter : Fin 2 → Label
  | innerEmit : Fin 2 → Label
  | loop : InnerLabel → Label
  | resultScan : Fin 3 → Label
  | resultRestore : Fin 3 → Label
  | append : GroupOutput.Label → Label
  | outerMove : Fin 4 → Label
  | outerDelimiter : Fin 4 → Label
  | outerEmit : Fin 4 → Label
  | done | bad
  deriving DecidableEq, Fintype

def innerStacks : InnerStack ↪ Stack := ⟨Sum.inl, by intro a b h; exact Sum.inl.inj h⟩
def random : Stack := .inl (Iteration.bodyStack SampleBody.machine SampleBody.random)
def counter : Stack := .inl (Iteration.counter SampleBody.machine)
def rows : Stack := .inr 0
def mass : Stack := .inr 1
def samples : Stack := .inr 2
def groups : Stack := .inr 3
def numerator : Stack := .inr 4
def scratch : Stack := .inr 5

def headerStack (i : Fin 4) : Stack := .inr ⟨i.val, by omega⟩
def headerNext (i : Fin 4) : Label :=
  match i.val with
  | 0 => .scan 1 | 1 => .scan 2 | 2 => .scan 3 | _ => .countMove

def innerField (i : Fin 2) : Stack := if i = 0 then mass else rows
def innerNext (i : Fin 2) : Label :=
  if i = 0 then .innerMove 1 else .loop (Iteration.own SampleBody.machine 0)

def resultField (i : Fin 3) : Stack :=
  match i.val with | 0 => rows | 1 => mass | _ => numerator
def resultNext (i : Fin 3) : Label :=
  match i.val with | 0 => .resultScan 1 | 1 => .resultScan 2 | _ => .append .append

def outerField (i : Fin 4) : Stack := .inr ⟨3 - i.val, by omega⟩
def outerNext (i : Fin 4) : Label :=
  match i.val with
  | 0 => .outerMove 1 | 1 => .outerMove 2 | 2 => .outerMove 3 | _ => .done

def appendStacks : GroupOutput.Stack ↪ Stack where
  toFun k := ![numerator, groups, scratch, samples] k
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;>
    simp_all [numerator, groups, scratch, samples]

def program : Label → Stmt Stack Label Memory
  | .scan i => Frame.scanStmt random scratch (.scan i) (.restore i) .bad
  | .restore i => copyMoveStmt scratch (headerStack i) (.restore i) (headerNext i)
  | .countMove => copyMoveStmt samples scratch .countMove .countRestore
  | .countRestore => copyRestoreStmt samples counter scratch .countRestore .innerZero
  | .innerZero => .push random (fun _ => false) (.goto (fun _ => .innerMove 0))
  | .innerMove i => copyMoveStmt (innerField i) scratch (.innerMove i) (.innerDelimiter i)
  | .innerDelimiter i => FrameEmit.delimiterStmt random (.innerEmit i)
  | .innerEmit i => FrameEmit.emitStmt scratch random (.innerEmit i) (innerNext i)
  | .loop l => Embedded.block innerStacks Label.loop (.resultScan 0)
      (Iteration.program SampleBody.machine l)
  | .resultScan i => Frame.scanStmt random scratch (.resultScan i) (.resultRestore i) .bad
  | .resultRestore i => copyMoveStmt scratch (resultField i) (.resultRestore i) (resultNext i)
  | .append l => MachineCall.block appendStacks Label.append (.outerMove 0)
      (MachineCall.unitState Memory) (GroupOutput.program l)
  | .outerMove i => copyMoveStmt (outerField i) scratch (.outerMove i) (.outerDelimiter i)
  | .outerDelimiter i => FrameEmit.delimiterStmt random (.outerEmit i)
  | .outerEmit i => FrameEmit.emitStmt scratch random (.outerEmit i) (outerNext i)
  | .done => .load (fun _ => initial) .halt
  | .bad => .load (fun _ => initial) .halt

def machine : Machine where
  K := Stack
  input := random
  output := random
  Label := Label
  main := .scan 0
  State := State
  initial := initial
  program := program

abbrev computer := machine.computer

theorem loop_code (l : InnerLabel) :
    program (.loop l) = Embedded.block innerStacks Label.loop (.resultScan 0)
      (Iteration.program SampleBody.machine l) := rfl

theorem append_code (l : GroupOutput.Label) :
    program (.append l) = MachineCall.block appendStacks Label.append (.outerMove 0)
      (MachineCall.unitState Memory) (GroupOutput.program l) := rfl

end Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
