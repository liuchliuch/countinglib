import Counting.Algorithm.KarpLubyRequest.ParameterCountsBank
import Counting.Algorithm.KarpLubyRequest.Dense.FormulaCall
import Counting.Algorithm.KarpLubyRequest.Sampling.TotalMassRun
import Counting.Algorithm.KarpLubyRequest.TapeBudget.Run
import Counting.Algorithm.KarpLubyRequest.ZeroBranchSpec

/-! Fixed, finite physical banks and register permutations for raw preparation.
The parameter validator shares its actual stacks with the count serializer.
All other source banks are disjoint; transfers between them are explicit code.
-/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol

abbrev FormulaMemory := Bool × IntegerArithmetic.CarryProtocol.Memory

instance parameterMemoryFinite : Fintype ParameterProgram.Memory := by
  letI := BinaryArithmetic.Comparison.computer.σFin
  exact inferInstanceAs (Fintype (Bool × BinaryArithmetic.Comparison.State))

instance formulaMemoryFinite : Fintype FormulaMemory := by
  letI := GraphPreprocessing.UnaryBinary.machine.computer.σFin
  exact inferInstanceAs (Fintype FormulaMemory)

instance massMemoryFinite : Fintype Sampling.TotalMass.Memory :=
  BinaryArithmetic.Addition.computer.σFin

instance countsMemoryFinite : Fintype ParameterCountsBank.Arithmetic.State :=
  ParameterCountsBank.Arithmetic.finiteState

instance budgetMemoryFinite : Fintype TapeBudget.Bank.Memory := by
  letI : Fintype TapeBudget.Bank.Engine.State := TapeBudget.Bank.Engine.finiteState
  exact inferInstanceAs (Fintype (TapeBudget.Bank.Status × TapeBudget.Bank.Engine.State))

set_option backward.isDefEq.respectTransparency false in
structure Memory where
  parameter : ParameterProgram.Memory
  counts : ParameterCountsBank.Arithmetic.State
  formula : FormulaMemory
  mass : Sampling.TotalMass.Memory
  budget : TapeBudget.Bank.Memory
  deriving Fintype

abbrev State := Option Bool × Memory
def initialMemory : Memory :=
  ⟨(false, BinaryArithmetic.Comparison.initial), ParameterCountsBank.Arithmetic.initial,
    (false, IntegerArithmetic.CarryProtocol.clean (false, false)),
    BinaryArithmetic.Addition.initial, ((false, false), TapeBudget.Bank.Engine.initial)⟩
def initial : State := (none, initialMemory)

abbrev WorkStack := ParameterCountsBank.Stack ⊕
  (Fin 13 ⊕ (Sampling.TotalMass.Stack ⊕ (TapeBudget.Bank.Stack ⊕ Unit)))
abbrev Stack := WorkStack ⊕ Unit

instance stackFinite : Fintype Stack := inferInstanceAs (Fintype Stack)
instance stackDecidable : DecidableEq Stack := inferInstanceAs (DecidableEq Stack)

def countsStacks : ParameterCountsBank.Stack ↪ Stack :=
  ⟨fun k => .inl (.inl k), by intro a b h; exact Sum.inl.inj (Sum.inl.inj h)⟩
def parameterStacks : ParameterProgram.Stack ↪ Stack :=
  ⟨fun k => countsStacks (.inl k), by intro a b h; exact Sum.inl.inj (countsStacks.injective h)⟩
def formulaStacks : Fin 13 ↪ Stack :=
  ⟨fun k => .inl (.inr (.inl k)), by intro a b h; exact Sum.inl.inj (Sum.inr.inj (Sum.inl.inj h))⟩
def massStacks : Sampling.TotalMass.Stack ↪ Stack :=
  ⟨fun k => .inl (.inr (.inr (.inl k))),
    by intro a b h; exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inl.inj h)))⟩
def budgetStacks : TapeBudget.Bank.Stack ↪ Stack :=
  ⟨fun k => .inl (.inr (.inr (.inr (.inl k)))),
    by intro a b h; exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inl.inj h))))⟩
def scratch : Stack := .inl (.inr (.inr (.inr (.inr ()))))
def output : Stack := .inr ()

def header (k : ProblemHeader.Stack) : Stack :=
  parameterStacks (ParameterProgram.parserMap (RequestParser.headerMap k))
def variableSource : Stack := header ProblemHeader.destination
def formulaSource : Stack := header ProblemHeader.source
def tapeSource : Stack := header (.inl 0)
def countOutput : Stack := countsStacks (ParameterCountsBank.arithmeticMap ParameterCountsBank.Arithmetic.output)
def budgetOriginal (k : Fin 4) : Stack := budgetStacks (TapeBudget.Bank.original k)

abbrev ParameterSaved := ParameterCountsBank.Arithmetic.State ×
  (FormulaMemory × (Sampling.TotalMass.Memory × TapeBudget.Bank.Memory))
abbrev CountsSaved := FormulaMemory × (Sampling.TotalMass.Memory × TapeBudget.Bank.Memory)
abbrev FormulaSaved := ParameterProgram.Memory ×
  (ParameterCountsBank.Arithmetic.State × (Sampling.TotalMass.Memory × TapeBudget.Bank.Memory))
abbrev MassSaved := ParameterProgram.Memory ×
  (ParameterCountsBank.Arithmetic.State × (FormulaMemory × TapeBudget.Bank.Memory))
abbrev BudgetSaved := ParameterProgram.Memory ×
  (ParameterCountsBank.Arithmetic.State × (FormulaMemory × Sampling.TotalMass.Memory))

def parameterState : (ParameterProgram.State × ParameterSaved) ≃ State where
  toFun x := (x.1.1, ⟨x.1.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩)
  invFun x := ((x.1, x.2.parameter), x.2.counts, x.2.formula, x.2.mass, x.2.budget)
  left_inv := by rintro ⟨⟨a,b⟩,c,d,e,f⟩; rfl
  right_inv := by rintro ⟨a,⟨b,c,d,e,f⟩⟩; rfl

def countsState : (ParameterCountsBank.State × CountsSaved) ≃ State where
  toFun x := (x.1.1, ⟨x.1.2.1, x.1.2.2, x.2.1, x.2.2.1, x.2.2.2⟩)
  invFun x := ((x.1, x.2.parameter, x.2.counts), x.2.formula, x.2.mass, x.2.budget)
  left_inv := by rintro ⟨⟨a,b,c⟩,d,e,f⟩; rfl
  right_inv := by rintro ⟨a,⟨b,c,d,e,f⟩⟩; rfl

def formulaState : (Dense.Formula.Memory × FormulaSaved) ≃ State where
  toFun x := (x.1.1, ⟨x.2.1, x.2.2.1, x.1.2, x.2.2.2.1, x.2.2.2.2⟩)
  invFun x := ((x.1, x.2.formula), x.2.parameter, x.2.counts, x.2.mass, x.2.budget)
  left_inv := by rintro ⟨⟨a,b⟩,c,d,e,f⟩; rfl
  right_inv := by rintro ⟨a,⟨b,c,d,e,f⟩⟩; rfl

def massState : (Sampling.TotalMass.State × MassSaved) ≃ State where
  toFun x := (x.1.1, ⟨x.2.1, x.2.2.1, x.2.2.2.1, x.1.2, x.2.2.2.2⟩)
  invFun x := ((x.1, x.2.mass), x.2.parameter, x.2.counts, x.2.formula, x.2.budget)
  left_inv := by rintro ⟨⟨a,b⟩,c,d,e,f⟩; rfl
  right_inv := by rintro ⟨a,⟨b,c,d,e,f⟩⟩; rfl

def budgetState : (TapeBudget.Bank.State × BudgetSaved) ≃ State where
  toFun x := (x.1.1, ⟨x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.1.2⟩)
  invFun x := ((x.1, x.2.budget), x.2.parameter, x.2.counts, x.2.formula, x.2.mass)
  left_inv := by rintro ⟨⟨a,b⟩,c,d,e,f⟩; rfl
  right_inv := by rintro ⟨a,⟨b,c,d,e,f⟩⟩; rfl

end
end Counting.Algorithm.KarpLubyRequest.Preparation
