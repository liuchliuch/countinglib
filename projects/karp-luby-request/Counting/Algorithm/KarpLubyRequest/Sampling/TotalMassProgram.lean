import Counting.Algorithm.KarpLubyRequest.Sampling.RowMass
import Counting.Algorithm.KarpLubyRequest.MachineCall
import Counting.Algorithm.KarpLubyRequest.Contract
import Holant.Complexity.BinaryArithmetic.Addition
import Holant.Complexity.GraphPreprocessing.Frame

/-!
# Actual sequential total-mass program

The input consists of the physically framed dense rows. Each iteration extracts
one row, calls the finite row-mass scanner, calls the existing H1 carry-adder,
and physically transfers its canonical result back to the accumulated-mass
stack. The row list is not decoded by a semantic callback. Empty input returns
the accumulated mass immediately, so the empty-DNF branch does no sample loop.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.TotalMass
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing

abbrev Stack := Fin 6
abbrev Label := Fin 11
abbrev Memory := BinaryArithmetic.Addition.State
abbrev State := Option Bool × Memory

/-- Framed rows, current row mass, total, extracted row, scratch, addition output. -/
def tapes (source mass total row work output : List Bool) : Stack → List Bool :=
  ![source, mass, total, row, work, output]

def config (label : Label) (source mass total row work output : List Bool) : Cfg Stack Label Memory :=
  cfg label BinaryArithmetic.Addition.initial (tapes source mass total row work output)

def finished (total : List Bool) : Cfg Stack Label Memory :=
  ⟨none, (none, BinaryArithmetic.Addition.initial), tapes [] [] total [] [] []⟩

def massStacks : RowMass.Stack ↪ Stack :=
  ⟨fun k => ![3, 1] k, by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
def massLabel (label : RowMass.Label) : Label := ⟨label.val + 3, by omega⟩
def massState : ((Option Bool × Unit) × Memory) ≃ State := MachineCall.unitState Memory

def additionStacks : BinaryArithmetic.Addition.Stack ↪ Stack :=
  ⟨fun k => match k with
    | .left => 2
    | .right => 1
    | .work => 4
    | .out => 5,
    by intro a b h; cases a <;> cases b <;> simp_all⟩
def additionLabel (label : Bool) : Label := if label then 7 else 6
def additionState : (Memory × Option Bool) ≃ State := Equiv.prodComm _ _

def loop : Stmt Stack Label Memory :=
  .peek 0 (fun v bit => (bit, v.2))
    (.branch (fun v => v.1.isSome)
      (.load (fun v => (none, v.2)) (.goto (fun _ => 1)))
      (.load (fun v => (none, v.2)) .halt))

def program (label : Label) : Stmt Stack Label Memory :=
  if label = 0 then loop
  else if label = 1 then Frame.scanStmt 0 4 1 2 10
  else if label = 2 then copyMoveStmt 4 3 2 3
  else if label = 3 then MachineCall.block massStacks massLabel 6 massState (RowMass.program 0)
  else if label = 4 then MachineCall.block massStacks massLabel 6 massState (RowMass.program 1)
  else if label = 5 then MachineCall.block massStacks massLabel 6 massState (RowMass.program 2)
  else if label = 6 then
    MachineCall.block additionStacks additionLabel 8 additionState (BinaryArithmetic.Addition.program false)
  else if label = 7 then
    MachineCall.block additionStacks additionLabel 8 additionState (BinaryArithmetic.Addition.program true)
  else if label = 8 then copyMoveStmt 5 4 8 9
  else if label = 9 then copyMoveStmt 4 2 9 0
  else .halt

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
    program (massLabel label) = MachineCall.block massStacks massLabel 6 massState (RowMass.program label) := by
  fin_cases label <;> rfl

theorem addition_code (label : Bool) :
    program (additionLabel label) = MachineCall.block additionStacks additionLabel 8 additionState
      (BinaryArithmetic.Addition.program label) := by
  cases label <;> rfl

theorem statement_budget (label : Label) : TM2Cost.budget (program label) ≤ 8 := by
  fin_cases label <;>
    simp only [program, Fin.reduceEq, ↓reduceIte, MachineCall.budget]
  all_goals first
    | exact (RowMass.statement_budget _).trans (by decide)
    | exact (BinaryArithmetic.Addition.program_budget _).trans (by decide)
    | decide

end Counting.Algorithm.KarpLubyRequest.Sampling.TotalMass
