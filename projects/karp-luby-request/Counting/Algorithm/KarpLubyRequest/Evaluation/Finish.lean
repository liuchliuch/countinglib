import Counting.Algorithm.KarpLubyRequest.Evaluation.Calls
import Counting.Algorithm.KarpLubyRequest.GroupOutput.Run

/-! # The real group-word finisher supplies the physical median input -/
namespace Counting.Algorithm.KarpLubyRequest.Evaluation
open Turing Computability Holant.Complexity StackProtocol BinaryCompose

set_option backward.isDefEq.respectTransparency false

def groupInputData (outer : OuterStack → List Bool) (r m s : List Bool) (xs : List ℕ) : Data :=
  { outer := outer
    fields := fieldWords r m s (encodeNat xs.length) (GroupOutput.reversed xs) [] }

def medianInputData (outer : OuterStack → List Bool) (r m s : List Bool) (xs : List ℕ) : Data :=
  { outer := outer
    fields := fieldWords r m s [] [] []
    median := wordTape Median.Program.Stack.input (Median.input xs) }

theorem group_finish_code (label : GroupOutput.Label) :
    program (.groupFinish label) = MachineCall.block groupOutputStacks Label.groupFinish .medianStart
      (MachineCall.unitState Memory) (GroupOutput.program label) := rfl

/-- The final reversal restores occurrence order and the actual stored count
is framed in front. The four shared source stacks are consumed or populated
exactly as specified; the complete outer bank is preserved. -/
theorem group_finish (outer : OuterStack → List Bool) (memory : Memory)
    (r m s : List Bool) (xs : List ℕ) :
    RunsExactly computer.step
      (configuration (.groupFinish .reverse) (none, memory) (groupInputData outer r m s xs))
      (configuration .medianStart (none, memory) (medianInputData outer r m s xs))
      ((Median.input xs).length + 4) := by
  apply MachineCall.run groupOutputStacks Label.groupFinish .medianStart (MachineCall.unitState Memory)
    GroupOutput.program program group_finish_code memory (groupInputData outer r m s xs).tapes
    (cfg .reverse () (GroupOutput.bank [] (GroupOutput.reversed xs) [] (encodeNat xs.length)))
    ⟨none, (none, ()), GroupOutput.bank (Median.input xs) [] [] []⟩
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro k hk; rfl
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro k hk
      rcases k with k | (k | (k | k))
      · rfl
      · fin_cases k <;> first
        | rfl
        | exact False.elim (hk 1 rfl)
        | exact False.elim (hk 2 rfl)
        | exact False.elim (hk 3 rfl)
      · cases k <;> first | rfl | exact False.elim (hk 0 rfl)
      · rfl
  · have source := GroupOutput.finish_run xs
    rw [GroupOutput.finish_cost] at source
    exact source

/-- A real load resets the finite median registers before its complete call. -/
theorem median_start (state : State) (d : Data) :
    computer.step (configuration .medianStart state d) =
      some (configuration (.median Median.Program.computer.main) initial d) := rfl

end Counting.Algorithm.KarpLubyRequest.Evaluation
