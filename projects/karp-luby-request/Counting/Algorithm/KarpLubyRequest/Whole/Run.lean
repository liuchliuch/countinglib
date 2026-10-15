import Counting.Algorithm.KarpLubyRequest.Whole.Composition
import Counting.Algorithm.KarpLubyRequest.Whole.ValueBridge
import Counting.Algorithm.KarpLubyRequest.Preparation.Classification

/-!
# Exact all-raw execution of the entire request

This is one finite program on the original raw request word, including arbitrary
malformed and noncanonical words. Its output is the original total evaluator's
literal rational codec. Execution and polynomial cost are separate theorems.
-/
namespace Counting.Algorithm.KarpLubyRequest.Whole
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

/-- Every original raw request has the original literal output under the actual
composed source, with all work stacks empty and finite registers reset. -/
theorem run (raw : List Bool) :
    ∃ time, RunsExactly computer.step (initList computer raw)
      (haltList computer (ProgramEncoding.evalBits raw)) time := by
  obtain ⟨prepareTime, hp⟩ := Preparation.raw_run raw
  rw [Preparation.halt_eq] at hp
  rcases Preparation.rawResult_classification raw with ⟨hz, hv⟩ |
    ⟨r, hd, hvalid, hmass, hlen, hresult⟩
  · rw [hz] at hp
    have he := Evaluation.zero_run
    have hr := compose_run raw [false] _ prepareTime 2 hp he
    rw [← hv] at hr
    exact ⟨_, hr⟩
  · rw [hresult] at hp
    rw [← ValueBridge.originalRows_mass r] at hp
    obtain ⟨time, _, hr⟩ := accepted_run raw r.problem.variableCount
      (ValueBridge.originalRows r) (ValueBridge.originalRows_lengths r)
      (Program.requestedSamples (DNF.normalizeFormula r.problem.formula) r.epsilon)
      (Program.requestedGroups r.delta) r.tape (ValueBridge.originalRows_tape r hlen)
      prepareTime hp
    rw [ValueBridge.output_eq_evalBits raw r hd hvalid hlen] at hr
    exact ⟨time, hr⟩

end
end Counting.Algorithm.KarpLubyRequest.Whole

