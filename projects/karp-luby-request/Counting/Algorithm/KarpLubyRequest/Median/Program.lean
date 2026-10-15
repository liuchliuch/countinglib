import Counting.Algorithm.KarpLubyRequest.StateAdapter
import Counting.Algorithm.KarpLubyRequest.Contract
import Holant.Complexity.BinaryArithmetic.Comparison

/-!
# The finite binary-stack upper-median program

All unbounded data live on twelve Boolean stacks. The only persistent control
bits say whether a minimum has been selected and whether the current candidate
has a strict majority. Unsigned comparison is the existing H1 source program,
inlined by the canonical state/stack compiler. Input is the canonical internal
list codec; malformed external-request validation belongs to the parser.
-/
namespace Counting.Algorithm.KarpLubyRequest.Median.Program
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Turing.TM2.Stmt

inductive Stack
  | input | saved | inner | candidate | chosen | left | right | work | answer | temp | below | above
  deriving DecidableEq, Fintype

inductive CopyJob
  | save | inner | countLeft | minLeft | minRight | chosen
  deriving DecidableEq, Fintype
inductive FrameJob
  | header | candidate | member
  deriving DecidableEq, Fintype
inductive ClearJob
  | header | below | above | chosen | candidate | saved
  deriving DecidableEq, Fintype
inductive Label
  | copyMove (job : CopyJob) | copyRestore (job : CopyJob)
  | scan (job : FrameJob) | restore (job : FrameJob) | clear (job : ClearJob)
  | outer | inner | compare (minimum : Bool) | mark | balance | choose | minimum | record | finish | bad
  deriving DecidableEq, Fintype

abbrev Memory := (Bool × Bool) × BinaryArithmetic.Comparison.State
abbrev State := Option Bool × Memory
instance stateFinite : Fintype State := by
  letI : Fintype BinaryArithmetic.Comparison.State := BinaryArithmetic.Comparison.computer.σFin
  exact inferInstanceAs (Fintype (Option Bool × ((Bool × Bool) × BinaryArithmetic.Comparison.State)))

def memory (selected eligible : Bool) : Memory :=
  ((selected, eligible), BinaryArithmetic.Comparison.initial)

def copySrc : CopyJob → Stack
  | .save => .input | .inner => .saved
  | .countLeft | .minLeft | .chosen => .candidate | .minRight => .chosen
def copyDst : CopyJob → Stack
  | .save => .saved | .inner => .inner
  | .countLeft | .minLeft => .left | .minRight => .right | .chosen => .chosen
def copyNext : CopyJob → Label
  | .save => .outer | .inner => .inner | .countLeft => .compare false
  | .minLeft => .copyMove .minRight | .minRight => .compare true | .chosen => .record
def frameSrc : FrameJob → Stack
  | .header | .candidate => .input | .member => .inner
def frameDst : FrameJob → Stack
  | .header | .member => .right | .candidate => .candidate
def frameNext : FrameJob → Label
  | .header => .clear .header | .candidate => .copyMove .inner | .member => .copyMove .countLeft
def clearStack : ClearJob → Stack
  | .header => .right | .below => .below | .above => .above
  | .chosen => .chosen | .candidate => .candidate | .saved => .saved
def clearNext : ClearJob → Label
  | .header => .copyMove .save | .below => .clear .above | .above => .choose
  | .chosen => .copyMove .chosen | .candidate => .outer | .saved => .finish

def comparisonMap : BinaryArithmetic.Comparison.Stack ↪ Stack :=
  ⟨fun k => match k with
      | .left => .left | .right => .right | .work => .work | .out => .answer,
    by intro a b h; cases a <;> cases b <;> simp_all⟩
def comparisonState : (BinaryArithmetic.Comparison.State × (Option Bool × (Bool × Bool))) ≃ State :=
  (Equiv.prodComm _ _).trans (Equiv.prodAssoc _ _ _)
def compareLabel (minimum : Bool) (_ : Unit) : Label := .compare minimum
def compareReturn (minimum : Bool) : Label := if minimum then .minimum else .mark

def program : Label → Stmt Stack Label Memory
  | .copyMove j => copyMoveStmt (copySrc j) .temp (.copyMove j) (.copyRestore j)
  | .copyRestore j => copyRestoreStmt (copySrc j) (copyDst j) .temp (.copyRestore j) (copyNext j)
  | .scan j => Frame.scanStmt (frameSrc j) .temp (.scan j) (.restore j) .bad
  | .restore j => copyMoveStmt .temp (frameDst j) (.restore j) (frameNext j)
  | .clear j => clearStmt (clearStack j) (.clear j) (clearNext j)
  | .outer => peek .input (fun v b => (b, v.2))
      (branch (fun v => v.1.isSome)
        (load (fun v => (none, v.2)) (goto (fun _ => .scan .candidate)))
        (load (fun v => (none, v.2)) (goto (fun _ => .clear .saved))))
  | .inner => peek .inner (fun v b => (b, v.2))
      (branch (fun v => v.1.isSome)
        (load (fun v => (none, v.2)) (goto (fun _ => .scan .member)))
        (load (fun v => (none, v.2)) (goto (fun _ => .balance))))
  | .compare minimum => Embedded.block comparisonMap (compareLabel minimum) (compareReturn minimum)
      (StateAdapter.block comparisonState (BinaryArithmetic.Comparison.computer.m ()))
  | .mark => pop .answer (fun v b => (b, v.2))
      (branch (fun v => v.1.getD false)
        (push .above (fun _ => true) (load (fun v => (none, v.2)) (goto (fun _ => .inner))))
        (push .below (fun _ => true) (load (fun v => (none, v.2)) (goto (fun _ => .inner)))))
  | .balance => pop .below (fun v b => (b, v.2))
      (branch (fun v => v.1.isSome)
        (pop .above (fun v b => (b, v.2))
          (branch (fun v => v.1.isSome)
            (load (fun v => (none, v.2)) (goto (fun _ => .balance)))
            (load (fun v => (none, (v.2.1.1, true), v.2.2)) (goto (fun _ => .clear .below)))))
        (load (fun v => (none, (v.2.1.1, false), v.2.2)) (goto (fun _ => .clear .below))))
  | .choose => branch (fun v => v.2.1.2)
      (branch (fun v => v.2.1.1) (goto (fun _ => .copyMove .minLeft))
        (goto (fun _ => .copyMove .chosen)))
      (goto (fun _ => .clear .candidate))
  | .minimum => pop .answer (fun v b => (b, v.2))
      (branch (fun v => v.1.getD false)
        (load (fun v => (none, v.2)) (goto (fun _ => .clear .chosen)))
        (load (fun v => (none, v.2)) (goto (fun _ => .clear .candidate))))
  | .record => load (fun v => (none, (true, v.2.1.2), v.2.2)) (goto (fun _ => .clear .candidate))
  | .finish | .bad => halt

abbrev computer : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .chosen
  Γ _ := Bool
  Λ := Label
  main := .scan .header
  σ := State
  initialState := (none, memory false false)
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

theorem statement_budget (l : Label) : TM2Cost.budget (program l) ≤ 9 := by
  cases l with
  | copyMove j => simp only [program, copyMoveStmt_budget]; decide
  | copyRestore j => simp only [program, copyRestoreStmt_budget]; decide
  | scan j => simp only [program, Frame.scanStmt_budget]; decide
  | restore j => simp only [program, copyMoveStmt_budget]; decide
  | clear j => simp only [program, clearStmt_budget]; decide
  | compare b =>
    simp only [program, Embedded.statement_budget, StateAdapter.statement_budget,
      BinaryArithmetic.Comparison.program_budget]
    decide
  | _ => decide

end Counting.Algorithm.KarpLubyRequest.Median.Program
