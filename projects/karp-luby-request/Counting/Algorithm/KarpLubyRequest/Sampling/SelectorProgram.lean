import Counting.Algorithm.KarpLubyRequest.Sampling.TotalMassRun
import Holant.Complexity.BinaryArithmetic.Comparison
import Holant.Complexity.BinaryArithmetic.Subtraction
import Holant.Complexity.FixedFieldMachines.FrameEmit

/-!
# Physical interval selection in the tagged clause union

The rank and each clause mass are canonical binary words. The program extracts
a row, preserves it while computing its mass, and physically copies the two
comparison operands. A failed interval test calls the existing subtractor and
prepends that row to a framed history stack. This history contains prior clause
occurrences in reverse order, which suffices for the later ownership `any` scan.
Neither the selected index nor an unbounded rank appears in finite control.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Selector
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing FixedFieldMachines

abbrev Stack := Fin 11
abbrev Label := Fin 23
abbrev Memory := BinaryArithmetic.Addition.State
abbrev State := Option Bool × Memory

/-- Rows, rank, row, mass, comparison operands, scratch, arithmetic work/output,
reverse framed history, disposable mass-scanner row. -/
def tapes (source rank row mass left right scratch work output history massRow : List Bool) :
    Stack → List Bool := fun k =>
  match k.val with
  | 0 => source
  | 1 => rank
  | 2 => row
  | 3 => mass
  | 4 => left
  | 5 => right
  | 6 => scratch
  | 7 => work
  | 8 => output
  | 9 => history
  | _ => massRow

def config (label : Label) (source rank row mass left right scratch work output history massRow : List Bool) :
    Cfg Stack Label Memory := cfg label BinaryArithmetic.Addition.initial
      (tapes source rank row mass left right scratch work output history massRow)

def massStacks : RowMass.Stack ↪ Stack :=
  ⟨fun k => ![10, 3] k, by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
def massLabel (label : RowMass.Label) : Label := ⟨label.val + 5, by omega⟩
def massState : ((Option Bool × Unit) × Memory) ≃ State := MachineCall.unitState Memory

def compareStacks : BinaryArithmetic.Addition.Stack ↪ Stack :=
  ⟨fun k => match k with | .left => 4 | .right => 5 | .work => 7 | .out => 8,
    by intro a b h; cases a <;> cases b <;> simp_all⟩
def compareLabel (_ : Unit) : Label := 12

def subtractStacks : BinaryArithmetic.Addition.Stack ↪ Stack :=
  ⟨fun k => match k with | .left => 1 | .right => 3 | .work => 7 | .out => 8,
    by intro a b h; cases a <;> cases b <;> simp_all⟩
def subtractLabel : BinaryArithmetic.Subtraction.Label → Label
  | .columns => 14
  | .trim => 15
  | .reverse => 16
  | .clear => 17
def arithmeticState : (Memory × Option Bool) ≃ State := Equiv.prodComm _ _

def loop : Stmt Stack Label Memory :=
  .peek 0 (fun v bit => (bit, v.2))
    (.branch (fun v => v.1.isSome)
      (.load (fun _ => (none, BinaryArithmetic.Addition.initial)) (.goto (fun _ => 1)))
      (.load (fun _ => (none, BinaryArithmetic.Addition.initial)) .halt))

def decideInterval : Stmt Stack Label Memory :=
  .pop 8 (fun v bit => (bit, v.2))
    (.branch (fun v => v.1.getD false)
      (.load (fun _ => (none, true, none, none)) .halt)
      (.load (fun _ => (none, BinaryArithmetic.Addition.initial)) (.goto (fun _ => 14))))

def program (label : Label) : Stmt Stack Label Memory :=
  if label = 0 then loop
  else if label = 1 then Frame.scanStmt 0 6 1 2 0
  else if label = 2 then copyMoveStmt 6 2 2 3
  else if label = 3 then copyMoveStmt 2 6 3 4
  else if label = 4 then copyRestoreStmt 2 10 6 4 5
  else if label = 5 then MachineCall.block massStacks massLabel 8 massState (RowMass.program 0)
  else if label = 6 then MachineCall.block massStacks massLabel 8 massState (RowMass.program 1)
  else if label = 7 then MachineCall.block massStacks massLabel 8 massState (RowMass.program 2)
  else if label = 8 then copyMoveStmt 1 6 8 9
  else if label = 9 then copyRestoreStmt 1 4 6 9 10
  else if label = 10 then copyMoveStmt 3 6 10 11
  else if label = 11 then copyRestoreStmt 3 5 6 11 12
  else if label = 12 then MachineCall.block compareStacks compareLabel 13 arithmeticState
    (BinaryArithmetic.Comparison.program ())
  else if label = 13 then decideInterval
  else if label = 14 then MachineCall.block subtractStacks subtractLabel 18 arithmeticState
    (BinaryArithmetic.Subtraction.program .columns)
  else if label = 15 then MachineCall.block subtractStacks subtractLabel 18 arithmeticState
    (BinaryArithmetic.Subtraction.program .trim)
  else if label = 16 then MachineCall.block subtractStacks subtractLabel 18 arithmeticState
    (BinaryArithmetic.Subtraction.program .reverse)
  else if label = 17 then MachineCall.block subtractStacks subtractLabel 18 arithmeticState
    (BinaryArithmetic.Subtraction.program .clear)
  else if label = 18 then copyMoveStmt 8 6 18 19
  else if label = 19 then copyMoveStmt 6 1 19 20
  else if label = 20 then copyMoveStmt 2 6 20 21
  else if label = 21 then FrameEmit.delimiterStmt 9 22
  else FrameEmit.emitStmt 6 9 22 0

abbrev computer : FinTM2 where
  K := Stack
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := 0
  σ := State
  initialState := (none, BinaryArithmetic.Addition.initial)
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

theorem mass_code (label : RowMass.Label) :
    program (massLabel label) = MachineCall.block massStacks massLabel 8 massState (RowMass.program label) := by
  fin_cases label <;> rfl

theorem comparison_code (label : Unit) :
    program (compareLabel label) = MachineCall.block compareStacks compareLabel 13 arithmeticState
      (BinaryArithmetic.Comparison.program label) := by cases label; rfl

theorem subtraction_code (label : BinaryArithmetic.Subtraction.Label) :
    program (subtractLabel label) = MachineCall.block subtractStacks subtractLabel 18 arithmeticState
      (BinaryArithmetic.Subtraction.program label) := by cases label <;> rfl

theorem statement_budget (label : Label) : TM2Cost.budget (program label) ≤ 8 := by
  fin_cases label <;> simp only [program, Fin.reduceEq, ↓reduceIte, MachineCall.budget]
  all_goals first
    | exact (RowMass.statement_budget _).trans (by decide)
    | exact (BinaryArithmetic.Subtraction.program_budget _).trans (by decide)
    | decide

end Counting.Algorithm.KarpLubyRequest.Sampling.Selector
