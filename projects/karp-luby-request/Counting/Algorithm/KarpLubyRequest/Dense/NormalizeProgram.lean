import Counting.Algorithm.KarpLubyRequest.Dense.LiteralWrite
import Counting.Algorithm.KarpLubyRequest.Dense.ReverseFrames

/-!
# Finite program for one raw DNF term

The original variable word stays on stack 0. Stack 1 is a disposable raw term;
stack 2 receives the dense row. Literal frames are physically reversed before
writes, matching the canonical tail-first normalizer. A contradictory suffix
clears all remaining literal frames before returning at the rejecting label.
-/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Normalize
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Turing.TM2.Stmt
open FixedFieldMachines

set_option backward.isDefEq.respectTransparency false in
inductive Label where
  | headerScan | headerRestore | headerClear
  | reverseCheck | reverseScan | reverseDelimiter | reverseEmit
  | allocateCopy | allocateRestore | allocateScan
  | loop | extractScan | extractRestore
  | literalScan | literalRestore | naturalMove | naturalHighest | naturalRestore | polarity
  | writeLoop | writeSkip | writeBorrow | writeRestoreCounter | writeApply | writeRestoreRow
  | writeClearCounter | writeClearPrefix | writeClearRow
  | rejectClear | good | bad
  deriving DecidableEq, Fintype

/-- Retained variable word, disposable raw word, row, raw index/unary work,
canonical index, reversed row pref, shared scratch, reversed literal stream. -/
def tapes (original source row raw counter pref scratch stream : List Bool) : Fin 8 → List Bool :=
  ![original, source, row, raw, counter, pref, scratch, stream]

def allocateStacks : Allocate.Stacks (Fin 8) :=
  ⟨![0, 3, 2, 6], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
def allocateLabels : Allocate.Labels Label :=
  ⟨.allocateCopy, .allocateRestore, .allocateScan, .loop⟩
def reverseStacks : ReverseFrames.Stacks (Fin 8) :=
  ⟨![1, 7, 6], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
def reverseLabels : ReverseFrames.Labels Label :=
  ⟨.reverseCheck, .reverseScan, .reverseDelimiter, .reverseEmit, .allocateCopy, .bad⟩
def literalStacks : LiteralWrite.Stacks (Fin 8) :=
  ⟨![1, 2, 3, 4, 5, 6], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
def writeLabels : Write.Labels Label :=
  ⟨.writeLoop, .writeSkip, .writeBorrow, .writeRestoreCounter, .writeApply,
    .writeRestoreRow, .writeClearCounter, .writeClearPrefix, .writeClearRow, .loop, .rejectClear⟩
def literalLabels : LiteralWrite.Labels Label :=
  ⟨.literalScan, .literalRestore, .naturalMove, .naturalHighest, .naturalRestore, .polarity, writeLabels⟩

@[simp] theorem allocateStacks_0 : allocateStacks 0 = 0 := rfl
@[simp] theorem allocateStacks_1 : allocateStacks 1 = 3 := rfl
@[simp] theorem allocateStacks_2 : allocateStacks 2 = 2 := rfl
@[simp] theorem allocateStacks_3 : allocateStacks 3 = 6 := rfl
@[simp] theorem reverseStacks_0 : reverseStacks 0 = 1 := rfl
@[simp] theorem reverseStacks_1 : reverseStacks 1 = 7 := rfl
@[simp] theorem reverseStacks_2 : reverseStacks 2 = 6 := rfl
@[simp] theorem literalStacks_0 : literalStacks 0 = 1 := rfl
@[simp] theorem literalStacks_1 : literalStacks 1 = 2 := rfl
@[simp] theorem literalStacks_2 : literalStacks 2 = 3 := rfl
@[simp] theorem literalStacks_3 : literalStacks 3 = 4 := rfl
@[simp] theorem literalStacks_4 : literalStacks 4 = 5 := rfl
@[simp] theorem literalStacks_5 : literalStacks 5 = 6 := rfl

/-- Every transition is one of the actual proved finite-stack instructions. -/
def program {τ : Type} : Label → Stmt (Fin 8) Label (Bool × τ)
  | .headerScan => Frame.scanStmt 1 6 .headerScan .headerRestore .bad
  | .headerRestore => copyMoveStmt 6 3 .headerRestore .headerClear
  | .headerClear => clearStmt 3 .headerClear .reverseCheck
  | .reverseCheck => ReverseFrames.checkStmt 1 .reverseScan .allocateCopy
  | .reverseScan => Frame.scanStmt 1 6 .reverseScan .reverseDelimiter .bad
  | .reverseDelimiter => FrameEmit.delimiterStmt 7 .reverseEmit
  | .reverseEmit => FrameEmit.emitStmt 6 7 .reverseEmit .reverseCheck
  | .allocateCopy => copyMoveStmt 0 6 .allocateCopy .allocateRestore
  | .allocateRestore => copyRestoreStmt 0 3 6 .allocateRestore .allocateScan
  | .allocateScan => Allocate.scanStmt 3 2 .allocateScan .loop
  | .loop => ReverseFrames.checkStmt 7 .extractScan .good
  | .extractScan => Frame.scanStmt 7 6 .extractScan .extractRestore .bad
  | .extractRestore => copyMoveStmt 6 1 .extractRestore .literalScan
  | .literalScan => Frame.scanStmt 1 6 .literalScan .literalRestore .rejectClear
  | .literalRestore => copyMoveStmt 6 3 .literalRestore .naturalMove
  | .naturalMove => copyMoveStmt 3 6 .naturalMove .naturalHighest
  | .naturalHighest => NaturalWords.highestStmt 6 4 .naturalRestore
  | .naturalRestore => copyMoveStmt 6 4 .naturalRestore .polarity
  | .polarity => LiteralWrite.polarityStmt 1 .writeLoop
  | .writeLoop => Write.checkStmt 2 4 .writeSkip .writeApply .writeClearCounter
  | .writeSkip => Write.skipStmt 2 5 .writeBorrow
  | .writeBorrow => CountedList.Counter.decrementStmt 4 6 .writeBorrow .writeRestoreCounter
  | .writeRestoreCounter => copyMoveStmt 6 4 .writeRestoreCounter .writeLoop
  | .writeApply => Write.writeStmt 2 .writeRestoreRow .writeClearCounter
  | .writeRestoreRow => copyMoveStmt 5 2 .writeRestoreRow .loop
  | .writeClearCounter => clearStmt 4 .writeClearCounter .writeClearPrefix
  | .writeClearPrefix => clearStmt 5 .writeClearPrefix .writeClearRow
  | .writeClearRow => clearStmt 2 .writeClearRow .rejectClear
  | .rejectClear => clearStmt 7 .rejectClear .bad
  | .good => load (fun v => (none, (true, v.2.2))) halt
  | .bad => load (fun v => (none, (false, v.2.2))) halt

abbrev computer : FinTM2 where
  K := Fin 8
  k₀ := 1
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := .headerScan
  σ := Option Bool × (Bool × Unit)
  initialState := (none, (false, ()))
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

theorem statement_budget {τ : Type} (l : Label) : TM2Cost.budget (program (τ := τ) l) ≤ 8 := by
  cases l <;> simp [program, TM2Cost.budget, Frame.scanStmt, copyMoveStmt, clearStmt,
    ReverseFrames.checkStmt, FrameEmit.delimiterStmt, FrameEmit.emitStmt, copyRestoreStmt,
    Allocate.scanStmt, NaturalWords.highestStmt, LiteralWrite.polarityStmt,
    Write.checkStmt, Write.skipStmt, CountedList.Counter.decrementStmt, Write.writeStmt]

theorem executes_allocate {τ : Type} :
    Allocate.Executes (TM2.step (program (τ := τ))) allocateStacks allocateLabels := by
  constructor <;> intro state tape <;> rfl

theorem executes_reverse {τ : Type} :
    ReverseFrames.Executes (TM2.step (program (τ := τ))) reverseStacks reverseLabels := by
  constructor <;> intro state tape <;> rfl

theorem executes_literal {τ : Type} :
    LiteralWrite.Executes (TM2.step (program (τ := τ))) literalStacks literalLabels := by
  constructor
  · intro state tape; rfl
  · intro state tape; rfl
  · constructor <;> intro state tape <;> rfl
  · intro state tape; rfl
  · constructor <;> intro state tape <;> rfl

end Counting.Algorithm.KarpLubyRequest.Dense.Normalize
