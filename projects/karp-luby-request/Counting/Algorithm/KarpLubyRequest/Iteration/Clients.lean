import Counting.Algorithm.KarpLubyRequest.Iteration.Cost
import Holant.Complexity.FixedFieldMachines.Reverse
import Holant.Complexity.GraphPreprocessing.FrameMachine

/-! Real executions cover zero repetition, empty/nonempty state words, a
nonidentity growing body with aliased input/output, and the canonical reversal
body with distinct input/output stacks. The observer executes the compiler's
actual statements; it is not an implementation of repeated source semantics. -/
namespace Counting.Algorithm.KarpLubyRequest.Iteration.Clients
open Turing Computability Holant.Complexity StackProtocol BinaryCompose FixedFieldMachines GraphPreprocessing
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

abbrev prependMachine : Machine where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Unit
  initial := ()
  program _ := .push () (fun _ => false) .halt

def prepend (word : List Bool) : List Bool := false :: word

theorem prepend_run (word : List Bool) : SourceRun prependMachine word (prepend word) 1 := by
  change prependMachine.computer.step (initList prependMachine.computer word) =
    some (haltList prependMachine.computer (prepend word))
  rw [Machine.init_eq, Machine.halt_eq]
  change some (⟨none, (), Function.update (wordTape () word) () (false :: wordTape () word ())⟩ : prependMachine.Config) = _
  rw [wordTape_at]
  have ht : Function.update (wordTape () word) () (false :: word) = wordTape () (false :: word) := by
    funext k; cases k; rfl
  rw [ht]
  rfl

theorem prepend_iterate (n : ℕ) (word : List Bool) :
    prepend^[n] word = List.replicate n false ++ word := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

example (n : ℕ) (word : List Bool) :
    RunsExactly (computer prependMachine).step
      (cfg (own prependMachine 0) prependMachine.initial (ready prependMachine (encodeNat n) word))
      (finished prependMachine (List.replicate n false ++ word))
      (ticks Frame.wordEncoding prepend (fun _ => 1) n word) := by
  have h := run prependMachine Frame.wordEncoding prepend (fun _ => 1) prepend_run n word
  rw [prepend_iterate] at h
  exact h

example (n : ℕ) (word : List Bool) :
    RunsExactly (computer Reverse.machine).step
      (cfg (own Reverse.machine 0) Reverse.machine.initial (ready Reverse.machine (encodeNat n) word))
      (finished Reverse.machine (List.reverse^[n] word))
      (ticks Frame.wordEncoding List.reverse (fun w => w.length + 2) n word) :=
  run Reverse.machine Frame.wordEncoding List.reverse (fun w => w.length + 2) Reverse.exact_run n word

/-- Observe actual source instructions with finite test fuel. -/
def observe (body : Machine) : ℕ → Config body → Option (ℕ × Config body)
  | 0, c => if c.l.isNone then some (0, c) else none
  | fuel + 1, c =>
    if c.l.isNone then some (0, c)
    else ((computer body).step c).bind fun next => (observe body fuel next).map fun p => (p.1 + 1, p.2)

def check (name : String) (body : Machine) [BEq body.State] (keys : List body.K)
    (f : List Bool → List Bool) (sourceTime : List Bool → ℕ) (n : ℕ) (word expected : List Bool) : IO Unit := do
  let start := cfg (own body 0) body.initial (ready body (encodeNat n) word)
  match observe body 200000 start with
  | none => throw (IO.userError (name ++ ": actual repeat compiler did not halt"))
  | some (time, ending) =>
    unless ending.stk (bodyStack body body.input) == expected do
      throw (IO.userError (name ++ ": incorrect repeated state word"))
    unless ending.var.1.isNone && ending.var.2 == body.initial do
      throw (IO.userError (name ++ ": finite source/caller state not reset"))
    unless (ending.stk (counter body)).isEmpty && (ending.stk (borrow body)).isEmpty &&
        (ending.stk (transfer body)).isEmpty &&
        keys.all (fun k => if k = body.input then true else (ending.stk (bodyStack body k)).isEmpty) do
      throw (IO.userError (name ++ ": a countdown or work stack was not cleared"))
    unless time == ticks Frame.wordEncoding f sourceTime n word do
      throw (IO.userError (name ++ ": exact transition charge mismatch"))
    let measured := Primitive.run (program body) time (some start)
    unless measured.1 ≤ (8 + body.primitiveBudget) * time do
      throw (IO.userError (name ++ ": primitive bound exceeded"))
    IO.println (name ++ ": " ++ toString time ++ " actual transitions, " ++
      toString measured.1 ++ " primitive instructions")

#eval check "zero count preserves nonempty state" prependMachine [()] prepend (fun _ => 1)
  0 [true, false, true] [true, false, true]
#eval check "growing body from empty state" prependMachine [()] prepend (fun _ => 1)
  3 [] [false, false, false]
#eval check "same input/output stack and binary borrow" prependMachine [()] prepend (fun _ => 1)
  8 [true] (List.replicate 8 false ++ [true])
#eval check "distinct stacks: one reversal" Reverse.machine [0, 1] List.reverse (fun w => w.length + 2)
  1 [true, false, false] [false, false, true]
#eval check "distinct stacks: two reversals" Reverse.machine [0, 1] List.reverse (fun w => w.length + 2)
  2 [true, false, false] [true, false, false]
#eval check "distinct stacks: empty state" Reverse.machine [0, 1] List.reverse (fun w => w.length + 2)
  7 [] []

end Counting.Algorithm.KarpLubyRequest.Iteration.Clients
