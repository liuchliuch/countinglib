import Counting.Algorithm.KarpLubyRequest.Sampling.TrialBank
import Holant.Complexity.FixedFieldMachines.FrameEmit
import Holant.Complexity.BinaryCompose.OutputBound

/-!
# A serialized sample-accumulation body

The input and output occupy the trial's random-tape stack. Three returning frame
extractors prepare rows, mass and accumulator. The actual trial program consumes
its physical random prefix; the H1 adder then consumes accumulator and numerator.
Three frame emitters rebuild the state word on the retained random suffix.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open FixedFieldMachines BinaryCompose

abbrev Stack := Trial.Stack ⊕ Fin 3
abbrev State := Trial.State
abbrev Memory := Trial.Memory

set_option backward.isDefEq.respectTransparency false in
inductive Label
  | scan : Fin 3 → Label
  | restore : Fin 3 → Label
  | trial : Trial.Label → Label
  | add : Bool → Label
  | move : Fin 3 → Label
  | delimiter : Fin 3 → Label
  | emit : Fin 3 → Label
  | done | bad
  deriving DecidableEq, Fintype

def trialStacks : Trial.Stack ↪ Stack :=
  ⟨Sum.inl, by intro a b h; exact Sum.inl.inj h⟩

def random : Stack := .inl .random
def scratch : Stack := .inl .scratch
def accumulator : Stack := .inr 0
def addWork : Stack := .inr 1
def addOutput : Stack := .inr 2

def headerStack (i : Fin 3) : Stack :=
  match i.val with
  | 0 => .inl .rows
  | 1 => .inl .mass
  | _ => accumulator

def headerNext (i : Fin 3) : Label :=
  match i.val with
  | 0 => .scan 1
  | 1 => .scan 2
  | _ => .trial .clockMove

def emitStack (i : Fin 3) : Stack :=
  match i.val with
  | 0 => addOutput
  | 1 => .inl .mass
  | _ => .inl .rows

def emitNext (i : Fin 3) : Label :=
  match i.val with
  | 0 => .move 1
  | 1 => .move 2
  | _ => .done

def additionStacks : BinaryArithmetic.Addition.Stack ↪ Stack where
  toFun
    | .left => accumulator
    | .right => .inl .output
    | .work => addWork
    | .out => addOutput
  inj' := by intro a b h; cases a <;> cases b <;> simp_all [accumulator, addWork, addOutput]

/-- Only a permutation of five finite registers is used. -/
def additionState : (BinaryArithmetic.Addition.State × (Option Bool × Bool)) ≃ State where
  toFun v := (v.2.1, v.1.2.1, v.1.2.2, v.1.1, v.2.2)
  invFun v := ((v.2.2.2.1, v.2.1, v.2.2.1), v.1, v.2.2.2.2)
  left_inv := by rintro ⟨⟨carry, left, right⟩, saved, flag⟩; rfl
  right_inv := by rintro ⟨saved, left, right, carry, flag⟩; rfl

def program : Label → Stmt Stack Label Memory
  | .scan i => Frame.scanStmt random scratch (.scan i) (.restore i) .bad
  | .restore i => copyMoveStmt scratch (headerStack i) (.restore i) (headerNext i)
  | .trial l => Embedded.block trialStacks Label.trial (.add false) (Trial.program l)
  | .add l => MachineCall.block additionStacks Label.add (.move 0) additionState
      (BinaryArithmetic.Addition.program l)
  | .move i => copyMoveStmt (emitStack i) scratch (.move i) (.delimiter i)
  | .delimiter i => FrameEmit.delimiterStmt random (.emit i)
  | .emit i => FrameEmit.emitStmt scratch random (.emit i) (emitNext i)
  | .done => .load (fun _ => Trial.initial) .halt
  | .bad => .load (fun _ => Trial.initial) .halt

/-- The repetition compiler can call the same physical input/output stack. -/
def machine : Machine where
  K := Stack
  input := random
  output := random
  Label := Label
  main := .scan 0
  State := State
  initial := Trial.initial
  program := program

abbrev computer := machine.computer

theorem trial_code (l : Trial.Label) :
    program (.trial l) = Embedded.block trialStacks Label.trial (.add false) (Trial.program l) := rfl

theorem addition_code (l : Bool) :
    program (.add l) = MachineCall.block additionStacks Label.add (.move 0) additionState
      (BinaryArithmetic.Addition.program l) := rfl

end Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
