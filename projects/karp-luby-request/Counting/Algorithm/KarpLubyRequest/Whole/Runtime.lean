import Counting.Algorithm.KarpLubyRequest.Preparation.Resources
import Counting.Algorithm.KarpLubyRequest.Preparation.RuntimeArithmetic
import Counting.Algorithm.KarpLubyRequest.Preparation.WorkEnumeration
import Counting.Algorithm.KarpLubyRequest.Evaluation.Clients

/-!
# Computable field views of the unchanged whole source

The arithmetic compiler specifications contain polynomial certificates. These
views project their existing finite instructions and registers without evaluating
those certificates or enumerating the product of finite register spaces. Every
program equation below is definitional equality, not a semantic replacement.
-/
namespace Counting.Algorithm.KarpLubyRequest.Whole.Runtime
open Turing Computability Holant.Complexity StackProtocol BinaryCompose GraphPreprocessing
open Preparation.RuntimeArithmetic
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 800000
set_option synthInstance.maxSize 10000

noncomputable abbrev sourceMachine : BinaryCompose.Machine :=
  Preparation.machine.compose Evaluation.machine

abbrev Stack := Preparation.Stack ⊕ (Evaluation.Stack ⊕ Unit)
abbrev Label := Preparation.Label ⊕ (Evaluation.Label ⊕ Bool)
abbrev State := Option Bool × (Preparation.State × Evaluation.State)
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Label State

/-- Only the displayed arithmetic program fields are used by these callers. -/
def countsBankProgram : ParameterCountsBank.Label →
    Stmt ParameterCountsBank.Stack ParameterCountsBank.Label ParameterCountsBank.Memory :=
  dsimp% (config := { unfoldPartialApp := true }) only [ParameterCountsBank.program, ParameterCountsBank.localProgram,
    ParameterCountsBank.code, ParameterCountsBank.destination, ParameterCountsBank.next,
    ← countsProgram_eq, ← countsInput_eq, ← countsMain_eq]
    ParameterCountsBank.program

theorem countsBankProgram_eq : countsBankProgram = ParameterCountsBank.program := rfl

def tapeBankProgram : TapeBudget.Bank.Label →
    Stmt TapeBudget.Bank.Stack TapeBudget.Bank.Label TapeBudget.Bank.Memory :=
  dsimp% (config := { unfoldPartialApp := true }) only [TapeBudget.Bank.program, TapeBudget.Bank.localProgram,
    TapeBudget.Bank.code, TapeBudget.Bank.destination, TapeBudget.Bank.next, TapeBudget.Bank.finish,
    ← tapeProgram_eq, ← tapeInput_eq, ← tapeOutput_eq, ← tapeMain_eq]
    TapeBudget.Bank.program

theorem tapeBankProgram_eq : tapeBankProgram = TapeBudget.Bank.program := rfl

def preparationInitial : Preparation.State :=
  (none, ⟨(false, BinaryArithmetic.Comparison.initial), countsInitial,
    (false, IntegerArithmetic.CarryProtocol.clean (false, false)),
    BinaryArithmetic.Addition.initial, ((false, false), tapeInitial)⟩)

theorem preparationInitial_eq : preparationInitial = Preparation.initial := rfl

def preparationProgram : Preparation.Label → Stmt Preparation.Stack Preparation.Label Preparation.Memory :=
  dsimp% (config := { unfoldPartialApp := true }) only [Preparation.program, Preparation.countOutput,
    ← countsBankProgram_eq, ← tapeBankProgram_eq, ← preparationInitial_eq, ← countsOutput_eq]
    Preparation.program

theorem preparationProgram_eq : preparationProgram = Preparation.program := rfl

set_option backward.dsimp.instances true in
/-- Unfold the canonical composition's field projections, retaining its exact
embedding and the same two physical handoff statements. -/
def program : Label → Statement :=
  dsimp% (config := { unfoldPartialApp := true }) only [sourceMachine, Machine.compose, Preparation.machine, Evaluation.machine,
    Machine.composeProgram, Machine.leftLayout, Machine.rightLayout,
    Machine.leftStates, Machine.rightStates, Machine.firstLabel, Machine.secondLabel,
    Machine.moveLabel, Machine.restoreLabel, Machine.sourceKey, Machine.destinationKey,
    Machine.temporaryKey, Preparation.stackDecidable, ParameterCountsBank.stackDecidable,
    TapeBudget.Bank.stackDecidable, ← countsDecidable_eq, ← tapeDecidable_eq,
    ← preparationProgram_eq, ← preparationInitial_eq]
    sourceMachine.program

theorem program_eq : program = sourceMachine.program := rfl

def initial : State := (none, preparationInitial, Evaluation.initial)

theorem initial_eq : initial = sourceMachine.initial := rfl

def main : Label := .inl (.parameter ParameterProgram.computer.main)
def input : Stack := .inl (Preparation.parameterStacks ParameterProgram.computer.k₀)
def output : Stack := .inr (.inl Evaluation.result)

theorem main_eq : main = sourceMachine.main := rfl
theorem input_eq : input = sourceMachine.input := rfl
theorem output_eq : output = sourceMachine.output := rfl

private def evaluationDecidable : DecidableEq Evaluation.Stack :=
  inferInstanceAs (DecidableEq
    (Evaluation.OuterStack ⊕ (Fin 6 ⊕ (Median.Program.Stack ⊕ Output.Program.Stack))))

private def evaluationEnumeration : FinEnum Evaluation.Stack :=
  @FinEnum.ofList Evaluation.Stack evaluationDecidable
    Evaluation.Clients.stackList Evaluation.Clients.stackList_complete

/-- This enumeration contains addresses only, including the handoff scratch. -/
def stackEnumeration : FinEnum Stack := by
  exact @FinEnum.sum Preparation.Stack (Evaluation.Stack ⊕ Unit)
    (@FinEnum.sum Preparation.WorkStack Unit Preparation.WorkEnumeration.enumeration FinEnum.punit)
    (@FinEnum.sum Evaluation.Stack Unit evaluationEnumeration FinEnum.punit)

def stackCount : ℕ := stackEnumeration.card
def stackEquiv : Fin stackCount ≃ Stack := stackEnumeration.equiv.symm
def stackDecidable : DecidableEq Stack := stackEnumeration.decEq

private def preparationMemoryDecidable : DecidableEq Preparation.Memory := by
  letI := countsStateDecidable
  letI := tapeStateDecidable
  intro a b
  cases a with | mk ap ac af am ab =>
    cases b with | mk bp bc bf bm bb =>
      exact decidable_of_iff (ap = bp ∧ ac = bc ∧ af = bf ∧ am = bm ∧ ab = bb)
        (by constructor <;> intro h
            · rcases h with ⟨rfl,rfl,rfl,rfl,rfl⟩; rfl
            · cases h; exact ⟨rfl,rfl,rfl,rfl,rfl⟩)

def stateDecidable : DecidableEq State := by
  repeat' first
  | exact preparationMemoryDecidable
  | exact Bool.decEq
  | exact instDecidableEqPUnit
  | refine @Option.instDecidableEq _ ?_
  | refine @instDecidableEqProd _ _ ?_ ?_

/-- Structural equality inspects every component of the finite memory tuple. -/
def stateBEq : BEq State := ⟨fun a b => @decide (a = b) (stateDecidable a b)⟩

def transition : sourceMachine.computer.Cfg → Option sourceMachine.computer.Cfg :=
  @TM2.step Stack (fun _ => Bool) Label State stackDecidable program

theorem transition_eq : transition = sourceMachine.computer.step := by
  have hd : stackDecidable = sourceMachine.decidableK := Subsingleton.elim _ _
  dsimp only [transition]
  rw [hd, program_eq]
  rfl

end Counting.Algorithm.KarpLubyRequest.Whole.Runtime
