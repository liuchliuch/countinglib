import Counting.Algorithm.KarpLubyRequest.Dense.NormalizeCall
import Counting.Algorithm.KarpLubyRequest.StateAdapter
import Holant.Complexity.GraphPreprocessing.UnaryBinary

/-!
# Finite program for dense normalization of a complete raw formula

Stacks 0 and 8 retain the original unary variable word and original raw formula.
The program consumes a physical copy, calls the complete finite term normalizer,
frames every successful row, and emits one real unary count token per row. The
row sequence is physically reversed once to restore original clause order. The
existing H1 unary-to-binary machine converts the real token stack to the output
count, so neither a count nor a literal index is held in finite control.
-/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Formula
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Turing.TM2.Stmt
open FixedFieldMachines IntegerArithmetic

set_option backward.isDefEq.respectTransparency false in
inductive Label where
  | copy | copyRestore | headerScan | headerRestore | headerClear
  | loop | extractScan | extractRestore | afterTerm
  | emitMove | emitDelimiter | emit | tally
  | reverseCheck | reverseScan | reverseDelimiter | reverseEmit
  | term (l : Normalize.Label)
  | count (l : Fin 4)
  | good | bad
  deriving DecidableEq, Fintype

abbrev Memory := Option Bool × (Bool × CarryProtocol.Memory)

instance memoryFinite : Fintype Memory := by
  letI : Fintype CarryProtocol.Memory := UnaryBinary.machine.computer.σFin
  exact inferInstanceAs (Fintype (Option Bool × (Bool × CarryProtocol.Memory)))

def termStacks : Fin 8 ↪ Fin 13 :=
  ⟨fun i => ⟨i.val, by omega⟩, by intro a b h; have hh := congrArg (fun z : Fin 13 => z.val) h; exact Fin.ext hh⟩

def countStacks : Fin 3 ↪ Fin 13 :=
  ⟨![11, 4, 6], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

def reverseStacks : ReverseFrames.Stacks (Fin 13) :=
  ⟨![10, 12, 6], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

def reverseLabels : ReverseFrames.Labels Label :=
  ⟨.reverseCheck, .reverseScan, .reverseDelimiter, .reverseEmit, .count 0, .bad⟩

/-- Reassociate the already finite arithmetic control and two saved Boolean
registers, without changing a stack or adding a transition. -/
def countState : CarryProtocol.Memory × (Option Bool × Bool) ≃ Memory where
  toFun v := (v.2.1, (v.2.2, v.1))
  invFun v := (v.2.2, (v.1, v.2.1))
  left_inv := by intro ⟨m, a, b⟩; rfl
  right_inv := by intro ⟨a, b, m⟩; rfl

def termBlock (l : Normalize.Label) : TM2.Stmt (fun _ : Fin 13 => Bool) Label Memory :=
  Embedded.block termStacks Label.term .afterTerm (Normalize.program (τ := CarryProtocol.Memory) l)

def countBlock (l : Fin 4) : TM2.Stmt (fun _ : Fin 13 => Bool) Label Memory :=
  Embedded.block countStacks Label.count .good
    (StateAdapter.block countState (UnaryBinary.machine.program l))

def program : Label → TM2.Stmt (fun _ : Fin 13 => Bool) Label Memory
  | .copy => copyMoveStmt 8 6 .copy .copyRestore
  | .copyRestore => copyRestoreStmt 8 9 6 .copyRestore .headerScan
  | .headerScan => Frame.scanStmt 9 6 .headerScan .headerRestore .bad
  | .headerRestore => copyMoveStmt 6 3 .headerRestore .headerClear
  | .headerClear => clearStmt 3 .headerClear .loop
  | .loop => ReverseFrames.checkStmt 9 .extractScan .reverseCheck
  | .extractScan => Frame.scanStmt 9 6 .extractScan .extractRestore .bad
  | .extractRestore => copyMoveStmt 6 1 .extractRestore (.term .headerScan)
  | .afterTerm => branch (fun v => v.2.1)
      (goto (fun _ => .emitMove)) (goto (fun _ => .loop))
  | .emitMove => copyMoveStmt 2 6 .emitMove .emitDelimiter
  | .emitDelimiter => FrameEmit.delimiterStmt 10 .emit
  | .emit => FrameEmit.emitStmt 6 10 .emit .tally
  | .tally => push 11 (fun _ => true) (goto (fun _ => .loop))
  | .reverseCheck => ReverseFrames.checkStmt 10 .reverseScan (.count 0)
  | .reverseScan => Frame.scanStmt 10 6 .reverseScan .reverseDelimiter .bad
  | .reverseDelimiter => FrameEmit.delimiterStmt 12 .reverseEmit
  | .reverseEmit => FrameEmit.emitStmt 6 12 .reverseEmit .reverseCheck
  | .term l => termBlock l
  | .count l => countBlock l
  | .good => halt
  | .bad => halt

abbrev computer : FinTM2 where
  K := Fin 13
  k₀ := 8
  k₁ := 12
  Γ _ := Bool
  Λ := Label
  main := .copy
  σ := Memory
  initialState := (none, (false, CarryProtocol.clean (false, false)))
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

theorem statement_budget (l : Label) : TM2Cost.budget (program l) ≤ 8 := by
  cases l with
  | term l =>
    simpa only [program, termBlock, Embedded.statement_budget] using
      Normalize.statement_budget (τ := CarryProtocol.Memory) l
  | count l =>
    rw [program, countBlock, Embedded.statement_budget, StateAdapter.statement_budget]
    exact (UnaryBinary.program_budget l).trans (by decide)
  | _ => decide

theorem executes_reverse : ReverseFrames.Executes computer.step reverseStacks reverseLabels := by
  constructor <;> intro state tape <;> rfl

end Counting.Algorithm.KarpLubyRequest.Dense.Formula
