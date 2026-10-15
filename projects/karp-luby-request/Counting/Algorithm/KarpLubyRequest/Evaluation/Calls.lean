import Counting.Algorithm.KarpLubyRequest.Evaluation.Bank
import Counting.Algorithm.KarpLubyRequest.Iteration.Orbit

/-!
# Three actual compiled calls in the post-validation evaluator

The group countdown, median selector, and rational normalizer are the already
installed finite programs. Complete source-bank replacement exposes all cleanup,
while the other three banks and every saved finite register are preserved.
-/
namespace Counting.Algorithm.KarpLubyRequest.Evaluation
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
open Counting.Algorithm.KarpLuby

set_option backward.isDefEq.respectTransparency false

theorem outer_code (label : OuterLabel) :
    program (.groups label) = MachineCall.block outerStacks Label.groups (.resultScan 0) outerState
      (Iteration.program Sampling.GroupBody.machine label) := rfl

theorem median_code (label : Median.Program.Label) :
    program (.median label) = MachineCall.block medianStacks Label.median .numMove medianState
      (Median.Program.program label) := rfl

theorem output_code (label : Output.Program.Label) :
    program (.output label) = MachineCall.block outputStacks Label.output .clearRow outputState
      (Output.Program.program label) := rfl

/-- This is only a compiler bridge for an execution of the fixed actual outer
countdown program. The caller instantiates it with the proved group-loop run. -/
theorem outer_call (d : Data)
    (saved : Option Bool × (Median.Program.State × Output.Program.State))
    (label : OuterLabel) (beforeState afterState : OuterState)
    (before after : OuterStack → List Bool) (time : ℕ)
    (source : RunsExactly (Iteration.computer Sampling.GroupBody.machine).step
      ⟨some label, beforeState, before⟩ ⟨none, afterState, after⟩ time) :
    RunsExactly computer.step
      (configuration (.groups label) (outerState (beforeState, saved)) {d with outer := before})
      (configuration (.resultScan 0) (outerState (afterState, saved)) {d with outer := after}) time := by
  apply MachineCall.run outerStacks Label.groups (.resultScan 0) outerState
    (Iteration.program Sampling.GroupBody.machine) program outer_code saved d.tapes
    ⟨some label, beforeState, before⟩ ⟨none, afterState, after⟩
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro k hk
      cases k with
      | inl k => exact False.elim (hk k rfl)
      | inr k => rfl
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro k hk
      cases k with
      | inl k => exact False.elim (hk k rfl)
      | inr k => rfl
  · exact source

/-- The physical natural-list input runs through the complete median program.
The returned selected/last flags are retained exactly, rather than reset by a
proof-side convention. Only the chosen word can remain in the median bank. -/
theorem median_call (d : Data)
    (saved : Option Bool × (OuterState × Output.Program.State)) (xs : List ℕ) :
    ∃ selected lastFlag time, time ≤ Median.timeBound (Median.input xs).length ∧
      RunsExactly computer.step
        (configuration (.median Median.Program.computer.main)
          (medianState (Median.Program.computer.initialState, saved))
          {d with median := (initList Median.Program.computer (Median.input xs)).stk})
        (configuration .numMove
          (medianState ((none, Median.Program.memory selected lastFlag), saved))
          {d with median := Median.Program.bank [] [] [] [] (encodeNat (Median.value xs)) 0 0}) time := by
  obtain ⟨selected, lastFlag, time, bound, source⟩ := Median.prepared_list xs
  refine ⟨selected, lastFlag, time, bound, ?_⟩
  apply MachineCall.run medianStacks Label.median .numMove medianState
    Median.Program.program program median_code saved d.tapes
    (initList Median.Program.computer (Median.input xs))
    ⟨none, (none, Median.Program.memory selected lastFlag),
      Median.Program.bank [] [] [] [] (encodeNat (Median.value xs)) 0 0⟩
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro k hk
      rcases k with k | (k | (k | k))
      · rfl
      · rfl
      · exact False.elim (hk k rfl)
      · rfl
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro k hk
      rcases k with k | (k | (k | k))
      · rfl
      · rfl
      · exact False.elim (hk k rfl)
      · rfl
  · exact source

/-- Separate canonical numerator/denominator words enter the original real
normalizer and serializer, producing the literal original rational codec.
The source state is restored, including when either component is zero. -/
theorem output_call (d : Data)
    (saved : Option Bool × (OuterState × Median.Program.State)) (a s : ℕ) :
    RunsExactly computer.step
      (configuration (.output (.inl (RationalArithmetic.Normalization.ph .start)))
        (outputState (Output.Program.computer.initialState, saved))
        {d with output := Output.Program.bank (encodeNat a) (encodeNat s) [] []})
      (configuration .clearRow (outputState (Output.Program.computer.initialState, saved))
        {d with output := wordTape Output.Program.computer.k₁ (Encoding.encodeOutput ((a : ℚ) / s))})
      (Output.componentTime a s) := by
  apply MachineCall.run outputStacks Label.output .clearRow outputState
    Output.Program.program program output_code saved d.tapes
    (cfg (.inl (RationalArithmetic.Normalization.ph .start)) Output.Program.initial
      (Output.Program.bank (encodeNat a) (encodeNat s) [] []))
    (haltList Output.Program.computer (Encoding.encodeOutput ((a : ℚ) / s)))
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro k hk
      rcases k with k | (k | (k | k))
      · rfl
      · rfl
      · rfl
      · exact False.elim (hk k rfl)
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k
      cases k with
      | inl k => cases k with
        | inl k => cases k <;> rfl
        | inr k => cases k <;> rfl
      | inr k => cases k <;> rfl
    · intro k hk
      rcases k with k | (k | (k | k))
      · rfl
      · rfl
      · rfl
      · exact False.elim (hk k rfl)
  · exact Output.prepared_components a s

end Counting.Algorithm.KarpLubyRequest.Evaluation
