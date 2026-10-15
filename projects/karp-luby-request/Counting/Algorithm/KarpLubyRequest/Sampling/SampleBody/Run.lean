import Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody.TrialCall
import Counting.Algorithm.KarpLubyRequest.Sampling.TrialRun
import Counting.Algorithm.KarpLubyRequest.Sampling.TapeIterationSpec
import Counting.Algorithm.KarpLubyRequest.Iteration.Stages

/-! # The complete serialized sample body executes the original trial -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

set_option backward.isDefEq.respectTransparency false

/-- Exact charges for three extracts, the concrete trial, canonical addition,
three emitters, and the final actual halt. -/
def bodyTime (rows mass : List Bool) (a b trialTime : ℕ) : ℕ :=
  2 * (rows.length + mass.length + (encodeNat a).length) + 6 + trialTime +
    additionTime a b + 2 * (rows.length + mass.length + (encodeNat (a + b)).length) + 10

theorem run_of_trial (rows mass input suffix : List Bool) (a b trialTime : ℕ)
    (trial : RunsExactly Trial.computer.step
      (Trial.configuration .clockMove Trial.initial (Trial.inputData rows mass input))
      (Trial.finalConfiguration rows mass suffix (encodeNat b)) trialTime) :
    RunsExactly computer.step
      (initList computer (word rows mass (encodeNat a) input))
      (haltList computer (word rows mass (encodeNat (a + b)) suffix))
      (bodyTime rows mass a b trialTime) := by
  rw [init_word, halt_word]
  have hp := prepare_exact rows mass (encodeNat a) input
  have ht := trial_call rows mass input suffix (encodeNat a) (encodeNat b) trialTime trial
  have ha := addition_exact rows mass suffix a b
  have hs := serialize_exact rows mass (encodeNat (a + b)) suffix
  convert ((hp.trans ht).trans ha).trans hs using 1 <;> dsimp only [bodyTime] <;> omega

/-- The iteration codec keeps the rows and canonical total mass physically in
front of the accumulator. Only the accumulator and unread tape vary along an orbit. -/
def stateEncoding (rows mass : List Bool) : Computability.Encoding (ℕ × List Bool) Bool where
  encode state := word rows mass (encodeNat state.1) state.2
  decode input := do
    let (_, rest) ← Encoding.unframe input
    let (_, rest) ← Encoding.unframe rest
    let (acc, suffix) ← Encoding.unframe rest
    return (Computability.decodeNat acc, suffix)
  decode_encode state := by
    rcases state with ⟨a, suffix⟩
    simp [word, List.append_assoc, Computability.decode_encodeNat]

/-- This time map is a theorem-side account of the displayed finite program. -/
def sourceTime (n : ℕ) (rows : List RowSemantics.Cells) (state : ℕ × List Bool) : ℕ :=
  let mass := encodeNat (TotalMass.rowSum rows)
  let bits := state.2.take mass.length
  let suffix := state.2.drop mass.length
  bodyTime (Dense.CellCodec.rows rows) mass state.1
    (Program.trial (rows.map (DenseNormalization.denote n)) (TapeIterationSpec.tapeValue bits))
    (Trial.runTime rows mass bits suffix)

/-- Every consumed random bit is present in the input word. The exact original
trial numerator is added, and the literal unread suffix is retained. -/
theorem source_run (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (state : ℕ × List Bool)
    (havailable : (encodeNat (TotalMass.rowSum rows)).length ≤ state.2.length) :
    Iteration.SourceRun machine
      ((stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))).encode state)
      ((stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))).encode
        (TapeIterationSpec.sampleStep (rows.map (DenseNormalization.denote n))
          (encodeNat (TotalMass.rowSum rows)).length state))
      (sourceTime n rows state) := by
  have ht := Trial.run_original n rows
    (state.2.take (encodeNat (TotalMass.rowSum rows)).length)
    (state.2.drop (encodeNat (TotalMass.rowSum rows)).length) hlen
    (by simpa only [List.length_take, Nat.min_eq_left havailable])
  rw [List.take_append_drop] at ht
  exact run_of_trial (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
    state.2 (state.2.drop (encodeNat (TotalMass.rowSum rows)).length) state.1
    (Program.trial (rows.map (DenseNormalization.denote n))
      (TapeIterationSpec.tapeValue (state.2.take (encodeNat (TotalMass.rowSum rows)).length)))
    (Trial.runTime rows (encodeNat (TotalMass.rowSum rows))
      (state.2.take (encodeNat (TotalMass.rowSum rows)).length)
      (state.2.drop (encodeNat (TotalMass.rowSum rows)).length)) ht

end Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
