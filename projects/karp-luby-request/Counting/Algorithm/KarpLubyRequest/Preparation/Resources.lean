import Counting.Algorithm.KarpLubyRequest.Preparation.Bank
import Holant.Complexity.BinaryCompose.OutputBound

/-! Physical stored-bit bounds for the very same preparation source. In
particular, even a rejecting raw-parser endpoint has no uncharged work words.
-/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose GraphPreprocessing

/-- A record view of the displayed source, with identical stacks, instructions,
registers and endpoints. This introduces no additional program or simulation. -/
def machine : BinaryCompose.Machine where
  K := Stack
  input := computer.k₀
  output := output
  Label := Label
  main := computer.main
  State := State
  initial := initial
  program := program

def primitiveBudget : ℕ := machine.primitiveBudget

theorem statement_budget (l : Label) : TM2Cost.budget (program l) ≤ primitiveBudget :=
  machine.program_budget_le l

/-- This bound follows from actual pushes executed along the given run. -/
theorem stored_bits (a z : computer.Cfg) (time : ℕ)
    (run : RunsExactly computer.step a z time) :
    stackSize z.stk ≤ stackSize a.stk + time * primitiveBudget :=
  machine.run_size_le a z time run

theorem stored_bits_from_raw (raw : List Bool) (z : computer.Cfg) (time : ℕ)
    (run : RunsExactly computer.step (initList computer raw) z time) :
    stackSize z.stk ≤ raw.length + time * primitiveBudget := by
  have h := stored_bits (initList computer raw) z time run
  have hi : stackSize (initList computer raw).stk = raw.length := machine.size_init raw
  rw [hi] at h
  exact h

theorem word_length_le (frame : Stack → List Bool) (k : Stack) :
    (frame k).length ≤ stackSize frame := by
  exact Finset.single_le_sum (f := fun k : Stack => (frame k).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

/-- The original primitive interpreter instruments the same physical run. -/
theorem primitive_run (a z : computer.Cfg) (time : ℕ)
    (run : RunsExactly computer.step a z time) :
    (Primitive.run program time (some a)).2 = some z ∧
    (Primitive.run program time (some a)).1 ≤ primitiveBudget * time :=
  Primitive.execution_cost program primitiveBudget statement_budget time a z run

end
end Counting.Algorithm.KarpLubyRequest.Preparation
