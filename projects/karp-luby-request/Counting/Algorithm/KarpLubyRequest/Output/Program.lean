import Counting.Algorithm.KarpLubyRequest.Output.Semantics
import Counting.Algorithm.KarpLubyRequest.MachineCall
import Holant.Complexity.FixedFieldMachines.FrameEmit

/-! Actual binary normalization followed by literal R1 output serialization.
Unbounded words reside on the existing fourteen Boolean stacks. Finite control
only routes the source normalizer and the scanning/reversal/framing loops. -/
namespace Counting.Algorithm.KarpLubyRequest.Output.Program
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Turing.TM2.Stmt
open RationalArithmetic IntegerArithmetic

abbrev Stack := Normalization.K
abbrev Memory := Normalization.Memory
abbrev State := Option Bool × Memory
instance stateFintype : Fintype State := by
  letI : Fintype Memory := Normalization.computer.σFin
  exact inferInstanceAs (Fintype (Option Bool × Memory))
inductive Phase
  | inputScan | inputRestore | denominatorReverse | denominatorRestore
  | componentScan | dropTag | moveDenominator | moveNumerator | delimiter | emit | sign | bad
  deriving DecidableEq, Fintype
abbrev Label := Normalization.Label ⊕ Phase
abbrev ph (p : Phase) : Label := .inr p
abbrev ex (p : Normalization.Extra) : Stack := Normalization.ex p

def initial : Memory := CarryProtocol.clean (false, false)
def normalizerState : Normalization.Memory × Option Bool ≃ State := Equiv.prodComm _ _

def program : Label → Stmt Stack Label Memory
  | .inl l => MachineCall.block (Function.Embedding.refl _) Sum.inl (ph .componentScan)
      normalizerState (Normalization.program l)
  | .inr .inputScan => Frame.scanStmt (ex .stream) (ex .temp)
      (ph .inputScan) (ph .inputRestore) (ph .bad)
  | .inr .inputRestore => copyMoveStmt (ex .temp) (ex .num)
      (ph .inputRestore) (ph .denominatorReverse)
  | .inr .denominatorReverse => copyMoveStmt (ex .stream) (ex .temp)
      (ph .denominatorReverse) (ph .denominatorRestore)
  | .inr .denominatorRestore => copyMoveStmt (ex .temp) (ex .den)
      (ph .denominatorRestore) (.inl (Normalization.ph .start))
  | .inr .componentScan => Frame.scanStmt (ex .stream) (ex .num)
      (ph .componentScan) (ph .dropTag) (ph .bad)
  | .inr .dropTag => pop (ex .num) (fun v _ => v) (goto (fun _ => ph .moveDenominator))
  | .inr .moveDenominator => copyMoveStmt (ex .stream) (ex .den)
      (ph .moveDenominator) (ph .moveNumerator)
  | .inr .moveNumerator => copyMoveStmt (ex .num) (ex .temp)
      (ph .moveNumerator) (ph .delimiter)
  | .inr .delimiter => FixedFieldMachines.FrameEmit.delimiterStmt (ex .den) (ph .emit)
  | .inr .emit => FixedFieldMachines.FrameEmit.emitStmt (ex .temp) (ex .den)
      (ph .emit) (ph .sign)
  | .inr .sign => push (ex .den) (fun _ => false) (push (ex .den) (fun _ => true)
      (push (ex .den) (fun _ => false) (push (ex .den) (fun _ => true)
        (push (ex .den) (fun _ => true) (push (ex .den) (fun _ => true) halt)))))
  | .inr .bad => halt

abbrev computer : FinTM2 where
  K := Stack
  k₀ := ex .stream
  k₁ := ex .den
  Γ _ := Bool
  Λ := Label
  main := ph .inputScan
  σ := State
  initialState := (none, initial)
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

theorem statement_budget (l : Label) : TM2Cost.budget (program l) ≤ 12 := by
  cases l with
  | inl l =>
    change TM2Cost.budget (MachineCall.block _ _ _ _ (Normalization.program l)) ≤ _
    rw [MachineCall.budget]
    exact Normalization.program_budget l
  | inr p => cases p <;> decide

end Counting.Algorithm.KarpLubyRequest.Output.Program
