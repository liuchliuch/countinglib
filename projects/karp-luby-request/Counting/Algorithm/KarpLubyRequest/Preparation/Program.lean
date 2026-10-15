import Counting.Algorithm.KarpLubyRequest.Preparation.WorkEnumeration

/-! One finite source program performs validation, dense normalization, mass and
parameter arithmetic, the exact tape gate, payload serialization and cleanup.
Every cross-bank transfer and every discarded reciprocal word is real code.
-/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing FixedFieldMachines

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

inductive CopyJob | variables | formula | rows | clauses | mass | tape
  deriving DecidableEq, Fintype

def workCount : ℕ := WorkEnumeration.count
theorem workCount_eq_card : workCount = Fintype.card WorkStack := WorkEnumeration.count_eq
theorem workCount_pos : 0 < workCount :=
  WorkEnumeration.count_pos
def workAt : Fin workCount ≃ WorkStack := WorkEnumeration.index

inductive Label
  | parameter : ParameterProgram.Label → Label
  | validated
  | copyMove : CopyJob → Label
  | copyRestore : CopyJob → Label
  | formula : Dense.Formula.Label → Label
  | mass : Sampling.TotalMass.Label → Label
  | massCheck
  | counts : ParameterCountsBank.Label → Label
  | dropScan : Fin 2 → Label
  | dropClear : Fin 2 → Label
  | sampleScan | sampleRestore | groupMove | groupRestore
  | budget : TapeBudget.Bank.Label → Label
  | gated | tapeMove | tapeRestore
  | emitMove : Fin 4 → Label
  | emitDelimiter : Fin 4 → Label
  | emit : Fin 4 → Label
  | positive | zero
  | clear : Fin workCount → Label
  | done
  deriving Fintype

def clearFirst : Label := .clear ⟨0, workCount_pos⟩
def clearNext (k : Fin workCount) : Label :=
  if h : k.val + 1 < workCount then .clear ⟨k.val + 1, h⟩ else .done

def copySource : CopyJob → Stack
  | .variables => variableSource
  | .formula => formulaSource
  | .rows => formulaStacks 12
  | .clauses => formulaStacks 4
  | .mass => massStacks 2
  | .tape => tapeSource
def copyDestination : CopyJob → Stack
  | .variables => formulaStacks 0
  | .formula => formulaStacks 8
  | .rows => massStacks 0
  | .clauses => countsStacks ParameterCountsBank.clauses
  | .mass => budgetOriginal 2
  | .tape => budgetOriginal 3
def copyNext : CopyJob → Label
  | .variables => .copyMove .formula
  | .formula => .formula .copy
  | .rows => .mass 0
  | .clauses => .counts (ParameterCountsBank.own 0)
  | .mass => .copyMove .tape
  | .tape => .budget (TapeBudget.Bank.own 0)

def dropNext (k : Fin 2) : Label := if k = 0 then .dropScan 1 else .sampleScan
def emitSource : Fin 4 → Stack := ![budgetOriginal 1, budgetOriginal 0, budgetOriginal 2, formulaStacks 12]
def emitNext (k : Fin 4) : Label :=
  if h : k.val + 1 < 4 then .emitMove ⟨k.val + 1, h⟩ else .positive

def program : Label → Stmt Stack Label Memory
  | .parameter l => MachineCall.block parameterStacks Label.parameter .validated
      parameterState (ParameterProgram.program l)
  | .validated => .branch (fun v => v.2.parameter.1)
      (.load (fun v => (none, v.2)) (.goto (fun _ => .copyMove .variables)))
      (.load (fun v => (none, v.2)) (.goto (fun _ => .zero)))
  | .copyMove j => copyMoveStmt (copySource j) scratch (.copyMove j) (.copyRestore j)
  | .copyRestore j => copyRestoreStmt (copySource j) (copyDestination j) scratch
      (.copyRestore j) (copyNext j)
  | .formula l => MachineCall.block formulaStacks Label.formula (.copyMove .rows)
      formulaState (Dense.Formula.program l)
  | .mass l => MachineCall.block massStacks Label.mass .massCheck
      massState (Sampling.TotalMass.program l)
  | .massCheck => .peek (massStacks 2) (fun v b => (b, v.2))
      (.branch (fun v => v.1.isSome)
        (.load (fun v => (none, v.2)) (.goto (fun _ => .copyMove .clauses)))
        (.load (fun v => (none, v.2)) (.goto (fun _ => .zero))))
  | .counts l => MachineCall.block countsStacks Label.counts (.dropScan 0)
      countsState (ParameterCountsBank.program l)
  | .dropScan k => Frame.scanStmt countOutput scratch (.dropScan k) (.dropClear k) .zero
  | .dropClear k => clearStmt scratch (.dropClear k) (dropNext k)
  | .sampleScan => Frame.scanStmt countOutput scratch .sampleScan .sampleRestore .zero
  | .sampleRestore => copyMoveStmt scratch (budgetOriginal 0) .sampleRestore .groupMove
  | .groupMove => copyMoveStmt countOutput scratch .groupMove .groupRestore
  | .groupRestore => copyMoveStmt scratch (budgetOriginal 1) .groupRestore (.copyMove .mass)
  | .budget l => MachineCall.block budgetStacks Label.budget .gated
      budgetState (TapeBudget.Bank.program l)
  | .gated => .branch (fun v => v.2.budget.1.1)
      (.load (fun v => (none, v.2)) (.goto (fun _ => .tapeMove)))
      (.load (fun v => (none, v.2)) (.goto (fun _ => .zero)))
  | .tapeMove => copyMoveStmt (budgetOriginal 3) scratch .tapeMove .tapeRestore
  | .tapeRestore => copyMoveStmt scratch output .tapeRestore (.emitMove 0)
  | .emitMove k => copyMoveStmt (emitSource k) scratch (.emitMove k) (.emitDelimiter k)
  | .emitDelimiter k => FrameEmit.delimiterStmt output (.emit k)
  | .emit k => FrameEmit.emitStmt scratch output (.emit k) (emitNext k)
  | .positive => .push output (fun _ => true) (.goto (fun _ => clearFirst))
  | .zero => .push output (fun _ => false) (.goto (fun _ => clearFirst))
  | .clear k => clearStmt (.inl (workAt k)) (.clear k) (clearNext k)
  | .done => .load (fun _ => initial) .halt

abbrev computer : FinTM2 where
  K := Stack
  k₀ := parameterStacks ParameterProgram.computer.k₀
  k₁ := output
  Γ _ := Bool
  Λ := Label
  main := .parameter ParameterProgram.computer.main
  σ := State
  initialState := initial
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

theorem parameter_code (l : ParameterProgram.Label) :
    program (.parameter l) = MachineCall.block parameterStacks Label.parameter .validated
      parameterState (ParameterProgram.program l) := rfl
theorem formula_code (l : Dense.Formula.Label) :
    program (.formula l) = MachineCall.block formulaStacks Label.formula (.copyMove .rows)
      formulaState (Dense.Formula.program l) := rfl
theorem mass_code (l : Sampling.TotalMass.Label) :
    program (.mass l) = MachineCall.block massStacks Label.mass .massCheck
      massState (Sampling.TotalMass.program l) := rfl
theorem counts_code (l : ParameterCountsBank.Label) :
    program (.counts l) = MachineCall.block countsStacks Label.counts (.dropScan 0)
      countsState (ParameterCountsBank.program l) := rfl
theorem budget_code (l : TapeBudget.Bank.Label) :
    program (.budget l) = MachineCall.block budgetStacks Label.budget .gated
      budgetState (TapeBudget.Bank.program l) := rfl

end
end Counting.Algorithm.KarpLubyRequest.Preparation
