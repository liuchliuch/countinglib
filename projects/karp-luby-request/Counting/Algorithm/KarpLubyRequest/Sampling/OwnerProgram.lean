import Counting.Algorithm.KarpLubyRequest.Sampling.RowEval
import Counting.Algorithm.KarpLubyRequest.MachineCall
import Counting.Algorithm.KarpLubyRequest.Contract

/-!
# Actual ownership scan over prior clause occurrences

The input history contains physical framed rows. Each iteration extracts one
row and copies the retained assignment before invoking the existing bit scanner.
No clause or assignment function is an instruction. A satisfied prior occurrence
rejects ownership; exhausted history accepts it. The caller supplies equal-width
rows and assignment, as produced by the selector and unranker.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Owner
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing

abbrev Stack := Fin 5
abbrev Label := Fin 7
abbrev Memory := Bool × Bool

/-- History, extracted row, retained assignment, disposable assignment, scratch. -/
def tapes (history row assignment disposable scratch : List Bool) : Stack → List Bool :=
  ![history, row, assignment, disposable, scratch]

def config (label : Label) (history row assignment disposable scratch : List Bool)
    (answer : Bool := true) : Cfg Stack Label Memory :=
  cfg label (false, answer) (tapes history row assignment disposable scratch)

def finished (answer : Bool) (history assignment : List Bool) : Cfg Stack Label Memory :=
  ⟨none, (none, false, answer), tapes history [] assignment [] []⟩

def rowStacks : RowEval.Stack ↪ Stack :=
  ⟨fun k => ![1, 3] k, by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
def rowLabel (_ : Unit) : Label := 5

def loop : Stmt Stack Label Memory :=
  .peek 0 (fun v bit => (bit, v.2))
    (.branch (fun v => v.1.isSome)
      (.load (fun _ => (none, false, true)) (.goto (fun _ => 1)))
      (.load (fun _ => (none, false, true)) .halt))

def tested : Stmt Stack Label Memory :=
  .branch (fun v => v.2.2)
    (.load (fun _ => (none, false, false)) .halt)
    (.load (fun _ => (none, false, true)) (.goto (fun _ => 0)))

def program (label : Label) : Stmt Stack Label Memory :=
  if label = 0 then loop
  else if label = 1 then Frame.scanStmt 0 4 1 2 0
  else if label = 2 then copyMoveStmt 4 1 2 3
  else if label = 3 then copyMoveStmt 2 4 3 4
  else if label = 4 then copyRestoreStmt 2 3 4 4 5
  else if label = 5 then Embedded.block rowStacks rowLabel 6 (RowEval.program ())
  else tested

abbrev computer : FinTM2 where
  K := Stack
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := 0
  σ := Option Bool × Memory
  initialState := (none, false, true)
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

theorem row_code (label : Unit) :
    program (rowLabel label) = Embedded.block rowStacks rowLabel 6 (RowEval.program label) := by
  cases label; rfl

theorem statement_budget (label : Label) : TM2Cost.budget (program label) ≤ 8 := by
  fin_cases label <;> simp only [program, Fin.reduceEq, ↓reduceIte, Embedded.statement_budget]
  all_goals first | exact (RowEval.statement_budget ()).trans (by decide) | decide

end Counting.Algorithm.KarpLubyRequest.Sampling.Owner
