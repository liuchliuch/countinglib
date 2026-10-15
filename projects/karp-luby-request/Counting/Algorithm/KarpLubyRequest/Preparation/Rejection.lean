import Counting.Algorithm.KarpLubyRequest.Preparation.DenseInput
import Counting.Algorithm.KarpLubyRequest.Preparation.Finish

/-! Complete malformed/invalid-parameter runs from a raw input. The original
parser is actually executed, then every retained field is physically cleared.
This covers arbitrary raw words and preserves the old evaluator's zero value. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

def rejectedBound (n : ℕ) : ℕ :=
  ParameterValidation.timeBound n + 1 +
    (n + (ParameterValidation.timeBound n + 1) * primitiveBudget) + workCount + 3

theorem rejected_value (raw : List Bool) (h : parameterStatus raw = false) :
    ProgramEncoding.evalBits raw = Encoding.encodeOutput 0 := by
  cases hd : ProgramEncoding.request.decode raw with
  | none => exact ProgramEncoding.evalBits_malformed raw hd
  | some r =>
    have hn : ¬ Program.ValidRequest r.epsilon r.delta := by
      dsimp only [parameterStatus] at h
      rw [hd] at h
      exact of_decide_eq_false h
    exact ZeroBranchSpec.evalBits_invalid_parameters raw r hd hn

/-- Every rejected raw parser/parameter word reaches the tagged-zero clean halt
under the original source program, including arbitrary dirty failure banks. -/
theorem rejected_run (raw : List Bool) (h : parameterStatus raw = false) :
    ∃ time, time ≤ rejectedBound raw.length ∧
      RunsExactly computer.step (initList computer raw) (finalConfiguration [false]) time := by
  obtain ⟨ending, parserTime, parserBound, parserRun, _⟩ := parameter_call raw
  rw [h] at parserRun
  let memory := {initialMemory with parameter := (false, BinaryArithmetic.Comparison.initial)}
  have dispatch := validated_false memory (parameterData ending).tapes rfl
  have prefixRun := parserRun.trans dispatch
  obtain ⟨endTime, endBound, endRun⟩ := zero_finish_bound memory (parameterData ending).tapes rfl
  have space := stored_bits_from_raw raw (cfg Label.zero memory (parameterData ending).tapes)
    (1 + parserTime) prefixRun
  have ht : 1 + parserTime ≤ ParameterValidation.timeBound raw.length + 1 := by
    simpa only [Nat.add_comm] using Nat.add_le_add_right parserBound 1
  have mono := Nat.mul_le_mul_right primitiveBudget ht
  refine ⟨endTime + (1 + parserTime), ?_, prefixRun.trans endRun⟩
  dsimp only [cfg] at space
  dsimp only [rejectedBound]
  have hs := space.trans (Nat.add_le_add_left mono raw.length)
  have he := endBound.trans (Nat.add_le_add_right (Nat.add_le_add_right hs workCount) 3)
  have total := Nat.add_le_add he ht
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using total

end
end Counting.Algorithm.KarpLubyRequest.Preparation
