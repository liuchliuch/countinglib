import Counting.Algorithm.KarpLubyRequest.CountedList
import Counting.Algorithm.KarpLubyRequest.MachineCall
import Holant.Complexity.BinaryCompose.OutputBound

/-!
# Repeating an actual finite Boolean-stack program

The countdown is a canonical binary word, never a natural-valued register.
Every positive iteration peeks and decrements that word, calls the entire
supplied finite body, and moves its clean output through two physical passes
back to its input stack. Input and output stack identifiers may coincide.
The zero branch halts immediately and preserves the current state word.

This compiler does not assume that an arbitrary body computes an estimator.
Its correctness theorem is conditional on actual clean source executions.
-/
namespace Counting.Algorithm.KarpLubyRequest.Iteration
open Turing Computability Holant.Complexity StackProtocol BinaryCompose

abbrev Stack (body : Machine) := Fin 3 ⊕ body.K
abbrev Label (body : Machine) := Fin 5 ⊕ body.Label
abbrev State (body : Machine) := Option Bool × body.State
abbrev Config (body : Machine) := Cfg (Stack body) (Label body) body.State

instance stackDecidable (body : Machine) : DecidableEq (Stack body) := inferInstanceAs (DecidableEq (Stack body))
instance stackFinite (body : Machine) : Fintype (Stack body) := inferInstanceAs (Fintype (Stack body))
instance labelFinite (body : Machine) : Fintype (Label body) := inferInstanceAs (Fintype (Label body))
instance stateFinite (body : Machine) : Fintype (State body) := inferInstanceAs (Fintype (State body))

def counter (body : Machine) : Stack body := .inl 0
def borrow (body : Machine) : Stack body := .inl 1
def transfer (body : Machine) : Stack body := .inl 2
def own (body : Machine) (label : Fin 5) : Label body := .inl label

def bodyStack (body : Machine) : body.K ↪ Stack body :=
  ⟨Sum.inr, by intro a b h; exact Sum.inr.inj h⟩
def bodyLabel (body : Machine) (label : body.Label) : Label body := .inr label

def bodyState (body : Machine) : (body.State × Option Bool) ≃ State body := Equiv.prodComm _ _

def check (body : Machine) : Stmt (Stack body) (Label body) body.State :=
  .peek (counter body) (fun v bit => (bit, v.2))
    (.branch (fun v => v.1.isSome)
      (.load (fun v => (none, v.2)) (.goto (fun _ => own body 1)))
      (.load (fun v => (none, v.2)) .halt))

def localProgram (body : Machine) (label : Fin 5) : Stmt (Stack body) (Label body) body.State :=
  if label = 0 then check body
  else if label = 1 then CountedList.Counter.decrementStmt (counter body) (borrow body) (own body 1) (own body 2)
  else if label = 2 then copyMoveStmt (borrow body) (counter body) (own body 2) (bodyLabel body body.main)
  else if label = 3 then copyMoveStmt (bodyStack body body.output) (transfer body) (own body 3) (own body 4)
  else copyMoveStmt (transfer body) (bodyStack body body.input) (own body 4) (own body 0)

def program (body : Machine) : Label body → Stmt (Stack body) (Label body) body.State
  | .inl label => localProgram body label
  | .inr label => MachineCall.block (bodyStack body) (bodyLabel body) (own body 3) (bodyState body)
      (body.program label)

/-- The exposed machine is called with a prepared binary counter in addition
to its state-word input; the execution theorem states this bank explicitly. -/
def machine (body : Machine) : Machine where
  K := Stack body
  input := bodyStack body body.input
  output := bodyStack body body.input
  Label := Label body
  main := own body 0
  State := State body
  initial := (none, body.initial)
  program := program body

abbrev computer (body : Machine) := (machine body).computer

def tapes (body : Machine) (count scratch word : List Bool) (source : body.K → List Bool) :
    Stack body → List Bool := Sum.elim (![count, scratch, word]) source

def ready (body : Machine) (count word : List Bool) : Stack body → List Bool :=
  tapes body count [] [] (wordTape body.input word)

def returned (body : Machine) (count word : List Bool) : Stack body → List Bool :=
  tapes body count [] [] (wordTape body.output word)

def moving (body : Machine) (count word : List Bool) : Stack body → List Bool :=
  tapes body count [] word (fun _ => [])

def finished (body : Machine) (word : List Bool) : Config body :=
  ⟨none, (none, body.initial), ready body [] word⟩

theorem body_code (body : Machine) (label : body.Label) :
    program body (bodyLabel body label) =
      MachineCall.block (bodyStack body) (bodyLabel body) (own body 3) (bodyState body) (body.program label) := rfl

theorem local_budget (body : Machine) (label : Fin 5) :
    TM2Cost.budget (localProgram body label) ≤ 8 := by
  fin_cases label
  · change (4 : ℕ) ≤ 8; decide
  · change (8 : ℕ) ≤ 8; decide
  · change (5 : ℕ) ≤ 8; decide
  · change (5 : ℕ) ≤ 8; decide
  · change (5 : ℕ) ≤ 8; decide

theorem program_budget (body : Machine) (label : Label body) :
    TM2Cost.budget (program body label) ≤ 8 + body.primitiveBudget := by
  cases label with
  | inl label => exact (local_budget body label).trans (Nat.le_add_right _ _)
  | inr label =>
    change TM2Cost.budget (MachineCall.block _ _ _ _ (body.program label)) ≤ _
    rw [MachineCall.budget]
    exact (body.program_budget_le label).trans (Nat.le_add_left _ _)

end Counting.Algorithm.KarpLubyRequest.Iteration
