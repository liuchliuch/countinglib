import Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody.Addition

/-! # An exact embedding of the unchanged finite trial program -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
open Turing Computability Holant.Complexity StackProtocol

set_option backward.isDefEq.respectTransparency false

/-- This composition lemma takes an execution of the displayed concrete trial
program, preserving the accumulator outside its stack embedding. The semantic
sample theorem instantiates this premise with the trial's proved actual run. -/
theorem trial_call (rows mass input suffix acc output : List Bool) (time : ℕ)
    (source : RunsExactly Trial.computer.step
      (Trial.configuration .clockMove Trial.initial (Trial.inputData rows mass input))
      (Trial.finalConfiguration rows mass suffix output) time) :
    RunsExactly computer.step
      (config (.trial .clockMove) (ready rows mass input acc []))
      (config (.add false) (ready rows mass suffix acc output)) time := by
  have initial : Embedded.Rel trialStacks Label.trial (.add false) (ready rows mass input acc [])
      (Trial.configuration .clockMove Trial.initial (Trial.inputData rows mass input))
      (config (.trial .clockMove) (ready rows mass input acc [])) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro k hk; rfl
  have final : Embedded.Rel trialStacks Label.trial (.add false) (ready rows mass input acc [])
      (Trial.finalConfiguration rows mass suffix output)
      (config (.add false) (ready rows mass suffix acc output)) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro k hk
      cases k with
      | inl k => exact False.elim (hk k rfl)
      | inr k => rfl
  obtain ⟨ending, actual, relation⟩ := Embedded.run trialStacks Label.trial (.add false)
    Trial.program program trial_code _ _ _ (ready rows mass input acc []) time initial source
  rw [MachineCall.rel_unique trialStacks Label.trial (.add false) _ _ ending _ relation final] at actual
  exact actual

end Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
