import Counting.Algorithm.KarpLubyRequest.Preparation.PositiveRun

/-! Complete accepted-parser continuation. Zero total mass branches directly to
cleanup before any sample/group arithmetic; positive mass executes the actual
count/gate pipeline and final codec serializer. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

def preparedResult (source : RequestParser.Stack → List Bool) (f : Formula source) : List Bool :=
  if Sampling.TotalMass.rowSum (normalizedRows source f) = 0 then [false] else positiveResult source f

def acceptedCost (source : RequestParser.Stack → List Bool) (f : Formula source) : ℕ :=
  normalizationCost source f + 1 + max
    (positivePrefixTime source f + 1 + max (finishBound (stackSize (gatedData source f).tapes))
      (stackSize (gatedData source f).tapes + workCount + 3))
    (stackSize (normalizedData source f).tapes + workCount + 3)

/-- Real complete continuation from the validator's own retained source bank.
No hypothesis supplies a normalization result, count output, gate flag or final
semantic equality. The only semantic input condition is the original decoder
of the raw formula word that the already executed parser accepted. -/
theorem accepted_run (source : RequestParser.Stack → List Bool) (f : Formula source)
    (hf : (Encoding.formula (variableWord source).length).decode (formulaWord source) = some f) :
    ∃ time, time ≤ acceptedCost source f ∧
      RunsExactly computer.step
        (configuration .validated (none, workingMemory false) (validatedData source))
        (finalConfiguration (preparedResult source f)) time := by
  obtain ⟨bit, normTime, normBound, normRun⟩ := normalize_mass source f hf
  by_cases hm : Sampling.TotalMass.rowSum (normalizedRows source f) = 0
  · have he : (normalizedData source f).tapes (massStacks 2) = [] := by
      change encodeNat (Sampling.TotalMass.rowSum (normalizedRows source f)) = []
      rw [hm]
      rfl
    have branch := mass_empty_branch (workingMemory bit) (normalizedData source f).tapes he
    obtain ⟨endTime, endBound, endRun⟩ := zero_finish_bound (workingMemory bit) (normalizedData source f).tapes rfl
    refine ⟨endTime + (1 + normTime), ?_, ?_⟩
    · have hm := Nat.le_max_right
        (positivePrefixTime source f + 1 + max (finishBound (stackSize (gatedData source f).tapes))
          (stackSize (gatedData source f).tapes + workCount + 3))
        (stackSize (normalizedData source f).tapes + workCount + 3)
      dsimp only [acceptedCost]
      have bound := Nat.add_le_add (endBound.trans hm) (Nat.add_le_add_left normBound 1)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
    · simpa only [preparedResult, hm, ite_true] using (normRun.trans branch).trans endRun
  · have he : (normalizedData source f).tapes (massStacks 2) ≠ [] := by
      intro he
      have hz : encodingNatBool.encode (Sampling.TotalMass.rowSum (normalizedRows source f)) =
          encodingNatBool.encode 0 := he
      exact hm (encodingNatBool.encode_injective hz)
    have branch := mass_nonempty_branch (workingMemory bit) (normalizedData source f).tapes he
    have counts := positive_prefix source f bit
    obtain ⟨endTime, endBound, endRun⟩ := finish_gate source f bit
    refine ⟨endTime + (positivePrefixTime source f + (1 + normTime)), ?_, ?_⟩
    · have hm := Nat.le_max_left
        (positivePrefixTime source f + 1 + max (finishBound (stackSize (gatedData source f).tapes))
          (stackSize (gatedData source f).tapes + workCount + 3))
        (stackSize (normalizedData source f).tapes + workCount + 3)
      dsimp only [acceptedCost]
      have partialBound : positivePrefixTime source f + endTime ≤
          positivePrefixTime source f + 1 +
            max (finishBound (stackSize (gatedData source f).tapes))
              (stackSize (gatedData source f).tapes + workCount + 3) := by
        simpa only [Nat.add_assoc] using Nat.add_le_add_left endBound (positivePrefixTime source f)
      have bound := Nat.add_le_add (partialBound.trans hm) (Nat.add_le_add_left normBound 1)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound
    · simpa only [preparedResult, hm, ite_false] using ((normRun.trans branch).trans counts).trans endRun

end
end Counting.Algorithm.KarpLubyRequest.Preparation
