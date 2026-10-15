import Counting.Algorithm.KarpLubyRequest.Preparation.Layout
import Mathlib.Data.FinEnum

/-! Computable enumeration of the fixed physical preparation bank.

The canonical `FinEnum` sum/finite-index constructions enumerate only stack
addresses. No enumeration of the product of finite machine registers is needed.
The cardinality bridge retains the existing `Fintype.card WorkStack` interface.
-/
namespace Counting.Algorithm.KarpLubyRequest.Preparation.WorkEnumeration
open Holant.Complexity BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false

@[instance_reducible] private def boolEnumeration : FinEnum Bool :=
  FinEnum.ofList [false, true] (by intro b; cases b <;> decide)

@[instance_reducible] private def additionEnumeration : FinEnum BinaryArithmetic.Addition.Stack :=
  FinEnum.ofList [.left, .right, .work, .out] (by intro k; cases k <;> decide)

@[instance_reducible] private def divisionEnumeration : FinEnum BinaryArithmetic.Division.Stack :=
  FinEnum.ofList [.input, .divisor, .remainder, .divisorRev, .oldRev, .trialRev, .quotient]
    (by intro k; cases k <;> decide)

attribute [local instance] boolEnumeration additionEnumeration divisionEnumeration

set_option synthInstance.maxHeartbeats 800000
set_option synthInstance.maxSize 10000
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
/-- Recursive canonical enumeration of every fixed physical work-stack address. -/
@[instance_reducible] def enumeration : FinEnum WorkStack := by
  dsimp only [WorkStack, ParameterCountsBank.Stack, ParameterCountsBank.Arithmetic,
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

/-- A computable loop bound, avoiding evaluation of a bundled machine's
noncomputable `Fintype` projection. -/
def count : ℕ := enumeration.card

/-- The actual computable address bijection used by the cleanup loop. -/
def index : Fin count ≃ WorkStack := enumeration.equiv.symm

theorem count_eq : count = Fintype.card WorkStack :=
  @FinEnum.card_eq_fintypeCard WorkStack enumeration inferInstance

theorem count_pos : 0 < count := by
  rw [count_eq]
  exact Fintype.card_pos_iff.mpr ⟨.inr (.inr (.inr (.inr ())))⟩

/-- A drop-in interface with the original cardinality index. The proof-only
cast does not inspect or enumerate machine states. -/
def workEquiv : Fin (Fintype.card WorkStack) ≃ WorkStack :=
  (Equiv.cast (congrArg Fin count_eq.symm)).trans index

/-- An executable exhaustive list, also suitable for checking the final bank. -/
def toList : List WorkStack := @FinEnum.toList WorkStack enumeration

theorem mem_toList (k : WorkStack) : k ∈ toList :=
  @FinEnum.mem_toList WorkStack enumeration k

theorem nodup_toList : toList.Nodup :=
  @FinEnum.nodup_toList WorkStack enumeration

theorem length_toList : toList.length = count := by
  change (List.map enumeration.equiv.symm (List.finRange count)).length = count
  exact (List.length_map _).trans List.length_finRange

end Counting.Algorithm.KarpLubyRequest.Preparation.WorkEnumeration
