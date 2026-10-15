import Counting.Algorithm.KarpLubyRequest.Whole.Runtime

/-! Candidate structural address enumeration for the exact runtime observer.
Only address representation changes: the displayed source program and its
physical cleanup enumeration are unchanged. -/
namespace Counting.Algorithm.KarpLubyRequest.Whole.Runtime.FastEnumeration
open Holant.Complexity BinaryCompose FixedFieldMachines
open Sampling
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option synthInstance.maxSize 10000
set_option maxRecDepth 1000000
set_option maxHeartbeats 1600000

/-- Sum addresses use a constructor test and an offset, not a whole-bank search. -/
@[instance_reducible] def fastSum {α β : Type} [a : FinEnum α] [b : FinEnum β] :
    FinEnum (α ⊕ β) where
  card := a.card + b.card
  equiv := (Equiv.sumCongr a.equiv b.equiv).trans finSumFinEquiv

/-- The original finite index is already its direct array address. -/
@[instance_reducible] def fastFin {n : ℕ} : FinEnum (Fin n) where
  card := n
  equiv := Equiv.refl _

attribute [local instance 2000] fastSum fastFin

@[instance_reducible] private def boolEnumeration : FinEnum Bool :=
  FinEnum.ofList [false, true] (by intro b; cases b <;> decide)

@[instance_reducible] private def additionEnumeration : FinEnum BinaryArithmetic.Addition.Stack :=
  FinEnum.ofList [.left, .right, .work, .out] (by intro k; cases k <;> decide)

@[instance_reducible] private def divisionEnumeration : FinEnum BinaryArithmetic.Division.Stack :=
  FinEnum.ofList [.input, .divisor, .remainder, .divisorRev, .oldRev, .trialRev, .quotient]
    (by intro k; cases k <;> decide)

attribute [local instance] boolEnumeration additionEnumeration divisionEnumeration

/-- The existing preparation address type with structural sum/index enumeration. -/
@[instance_reducible] def workEnumeration : FinEnum Preparation.WorkStack := by
  dsimp only [Preparation.WorkStack, ParameterCountsBank.Stack, ParameterCountsBank.Arithmetic,
      TapeBudget.Bank.Stack, TapeBudget.Bank.Engine, ParameterCounts.computes,
      ParameterCounts.epsilonReciprocal,
      ParameterCounts.deltaReciprocal,
      ParameterCounts.sampleCount,
      ParameterCounts.groupCount,
      ParameterCounts.reciprocalSquare,
      ParameterCounts.epsilonNumerator,
      ParameterCounts.epsilonDenominator,
      ParameterCounts.deltaNumerator,
      ParameterCounts.deltaDenominator,
      ParameterCounts.clauses,
      ParameterCounts.rest,
      ParameterCounts.tail,
      ParameterCounts.lastPair,
      ParameterCounts.quotient,
      ParameterCounts.quotientReversed,
      ParameterCounts.increment,
      ParameterCounts.add,
      ParameterCounts.multiply,
      ParameterCounts.arithmeticInput,
      ParameterCounts.bitLength,
      TapeBudget.Arithmetic.computes,
      TapeBudget.Arithmetic.tail,
      TapeBudget.Arithmetic.massTail,
      TapeBudget.Arithmetic.samples,
      TapeBudget.Arithmetic.groups,
      TapeBudget.Arithmetic.mass,
      TapeBudget.Arithmetic.tape,
      TapeBudget.Arithmetic.width,
      TapeBudget.Arithmetic.tapeLength,
      TapeBudget.Arithmetic.sampleWidth,
      TapeBudget.Arithmetic.budget,
      TapeBudget.Arithmetic.equal,
      TapeBudget.Arithmetic.wordLength,
      pairComputes,
      rightMapComputes,
      leftMapComputes,
      recode,
      congrComputes,
      Computes.andThen,
      Computes.comp,
      Wiring.secondComputes,
      Wiring.firstComputes,
      Wiring.swapComputes,
      Wiring.diagonalComputes,
      identityComputes,
      constantComputes,
      reverseComputes,
      additionComputes,
      multiplicationComputes,
      doublingComputes,
      Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.WordCompare.computes,
      Machine.composeProgram,
      Machine.leftLayout,
      Machine.rightLayout,
      Machine.leftStates,
      Machine.rightStates,
      Machine.firstLabel,
      Machine.secondLabel,
      Machine.moveLabel,
      Machine.restoreLabel,
      Machine.sourceKey,
      Machine.destinationKey,
      Machine.temporaryKey,
      LeftMap.program,
      LeftMap.layout,
      LeftMap.states, Machine.Keys, Machine.compose, LeftMap.Keys, LeftMap.machine,
      Wiring.firstMachine, Wiring.swapMachine, Wiring.diagonalMachine, Reverse.machine,
      identityMachine, Constant.machine, ParameterCounts.quotientMachine,
      additionMachine, multiplicationMachine, doublingMachine,
      BinaryArithmetic.EncodedDivision.computer, BinaryArithmetic.EncodedAddition.computer,
      BinaryArithmetic.EncodedMultiplication.computer, BinaryArithmetic.Doubling.computer,
      GraphPreprocessing.UnaryBinary.machine,
      Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.WordCompare.machine]
  infer_instance

@[instance_reducible] private def trialEnumeration : FinEnum Trial.Stack :=
  FinEnum.ofList
    [.rows, .mass, .random, .rank, .remaining, .row, .rowMass, .history, .clock, .left,
     .right, .work, .arithmeticOutput, .scratch, .massRow, .assignment, .assignmentCopy, .output]
    (by intro k; cases k <;> decide)

@[instance_reducible] private def medianEnumeration : FinEnum Median.Program.Stack :=
  FinEnum.ofList
    [.input, .saved, .inner, .candidate, .chosen, .left, .right, .work,
     .answer, .temp, .below, .above]
    (by intro k; cases k <;> decide)

private def outputList : List Output.Program.Stack :=
  [.inl (.inl .input), .inl (.inl .divisor), .inl (.inl .remainder),
   .inl (.inl .divisorRev), .inl (.inl .oldRev), .inl (.inl .trialRev),
   .inl (.inl .quotient), .inl (.inr .saved), .inl (.inr .temp),
   Output.Program.ex .num, Output.Program.ex .den, Output.Program.ex .temp,
   Output.Program.ex .gcd, Output.Program.ex .stream]

private theorem outputList_complete (k : Output.Program.Stack) : k ∈ outputList := by
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [outputList]
    | inr k => cases k <;> simp [outputList]
  | inr k => cases k <;> simp [outputList]

@[instance_reducible] private def outputEnumeration : FinEnum Output.Program.Stack :=
  FinEnum.ofList outputList outputList_complete

attribute [local instance] trialEnumeration medianEnumeration outputEnumeration

@[instance_reducible] def evaluationEnumeration : FinEnum Evaluation.Stack := by
  change FinEnum ((Fin 3 ⊕ ((Fin 3 ⊕ (Trial.Stack ⊕ Fin 3)) ⊕ Fin 6)) ⊕
    (Fin 6 ⊕ (Median.Program.Stack ⊕ Output.Program.Stack)))
  infer_instance

/-- Every whole-machine physical stack, including both outputs and handoff work. -/
@[instance_reducible] def enumeration : FinEnum Whole.Runtime.Stack :=
  @fastSum Preparation.Stack (Evaluation.Stack ⊕ Unit)
    (@fastSum Preparation.WorkStack Unit workEnumeration FinEnum.punit)
    (@fastSum Evaluation.Stack Unit evaluationEnumeration FinEnum.punit)

def count : ℕ := enumeration.card

def fastStackEquiv : Fin count ≃ Whole.Runtime.Stack := enumeration.equiv.symm

theorem covers (k : Whole.Runtime.Stack) : ∃ i : Fin count, fastStackEquiv i = k :=
  ⟨fastStackEquiv.symm k, fastStackEquiv.apply_symm_apply k⟩

theorem count_eq : count = 1392 := by decide

#eval count
#eval (List.finRange count).all fun i => fastStackEquiv.symm (fastStackEquiv i) == i

end Counting.Algorithm.KarpLubyRequest.Whole.Runtime.FastEnumeration
