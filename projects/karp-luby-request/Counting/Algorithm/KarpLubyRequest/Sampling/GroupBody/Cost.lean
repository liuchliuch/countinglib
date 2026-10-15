import Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Run
import Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody.Orbit

/-! # Physical size bounds for the complete group body

The numeric sample count multiplies the actual inner-loop charge. Its binary
length bounds only counters, arithmetic operands and framed numerator storage.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
open Turing Computability Holant.Complexity StackProtocol BinaryCompose GraphPreprocessing
open Counting.Algorithm.KarpLuby
open Counting.Algorithm.KarpLubyMachine
open TapeIterationSpec

theorem bodyTime_eq (rows mass samples history result : List Bool) (innerTime : ℕ) :
    bodyTime rows mass samples history result innerTime =
      innerTime + 8 * rows.length + 8 * mass.length + 6 * samples.length +
        4 * history.length + 7 * result.length + 39 := by
  simp only [bodyTime, List.length_append, List.length_reverse, Encoding.frame_length]
  omega

/-- An explicit arithmetic expression in physical lengths and numeric samples.
No claimed polynomial clock is inferred from a binary count's length alone. -/
def timeBound (rowLength width sampleBits historyLength tapeLength samples : ℕ) : ℕ :=
  1 + samples *
    ((220 * (rowLength + 2 * width + 1)^2 + 4 * rowLength + 14 * width + 6 * sampleBits + 31) +
      2 * ((2 * rowLength + 4 * width + 2 * sampleBits + 5 + tapeLength) + 1) +
      2 * sampleBits + 3) +
    8 * rowLength + 15 * width + 13 * sampleBits + 4 * historyLength + 46

theorem sourceTime_le (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (samples : ℕ) (state : List Bool × List Bool) :
    sourceTime n rows samples state ≤ timeBound (Dense.CellCodec.rows rows).length
      (encodeNat (TotalMass.rowSum rows)).length (encodeNat samples).length
      state.1.length state.2.length samples := by
  have ht := Iteration.ticks_le
    (SampleBody.stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)))
    (sampleStep (rows.map (DenseNormalization.denote n)) (encodeNat (TotalMass.rowSum rows)).length)
    (SampleBody.sourceTime n rows) samples (0, state.2)
    (220 * ((Dense.CellCodec.rows rows).length + 2 * (encodeNat (TotalMass.rowSum rows)).length + 1)^2 +
      4 * (Dense.CellCodec.rows rows).length + 14 * (encodeNat (TotalMass.rowSum rows)).length +
      6 * (encodeNat samples).length + 31)
    (2 * (Dense.CellCodec.rows rows).length + 4 * (encodeNat (TotalMass.rowSum rows)).length +
      2 * (encodeNat samples).length + 5 + state.2.length)
    (fun i hi => SampleBody.sourceTime_on_le n rows hlen samples state.2 i (by omega))
    (fun i hi => SampleBody.state_word_on_le n rows hlen samples state.2 (i+1) (by omega))
  have hr := TapeBounds.sample_accumulator_bits_le (rows.map (DenseNormalization.denote n))
    samples (encodeNat (TotalMass.rowSum rows)).length samples state.2 (by omega)
    (SampleBody.width_original n rows hlen)
  dsimp only [sourceTime]
  rw [bodyTime_eq]
  dsimp only [timeBound]
  omega

theorem state_word_length (rows mass samples : List Bool) (state : List Bool × List Bool) :
    ((stateEncoding rows mass samples).encode state).length =
      2 * rows.length + 2 * mass.length + 2 * samples.length + 2 * state.1.length + 4 + state.2.length := by
  change (word rows mass samples state.1 state.2).length = _
  simp only [word, List.length_append, Encoding.frame_length]
  omega

theorem next_word_le (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (samples : ℕ) (state : List Bool × List Bool) :
    ((stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
      (encodeNat samples)).encode (step (rows.map (DenseNormalization.denote n)) samples
        (encodeNat (TotalMass.rowSum rows)).length state)).length ≤
      2 * (Dense.CellCodec.rows rows).length + 6 * (encodeNat (TotalMass.rowSum rows)).length +
        6 * (encodeNat samples).length + 2 * state.1.length + 10 + state.2.length := by
  have hr := TapeBounds.sample_accumulator_bits_le (rows.map (DenseNormalization.denote n))
    samples (encodeNat (TotalMass.rowSum rows)).length samples state.2 (by omega)
    (SampleBody.width_original n rows hlen)
  rw [state_word_length]
  dsimp only [step]
  simp only [List.length_append, List.length_reverse, Encoding.frame_length]
  rw [sample_iterate_raw] at hr ⊢
  simp only [Nat.zero_add, List.length_drop] at hr ⊢
  omega

/-- The displayed physical-size bound charges the actual primitive interpreter
of the same group program and its complete nested sample execution. -/
theorem bounded_bit_cost (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (samples : ℕ) (state : List Bool × List Bool)
    (havailable : samples * (encodeNat (TotalMass.rowSum rows)).length ≤ state.2.length) :
    (Primitive.run program (sourceTime n rows samples state)
      (some (initList computer ((stateEncoding (Dense.CellCodec.rows rows)
        (encodeNat (TotalMass.rowSum rows)) (encodeNat samples)).encode state)))).1 ≤
      machine.primitiveBudget * timeBound (Dense.CellCodec.rows rows).length
        (encodeNat (TotalMass.rowSum rows)).length (encodeNat samples).length
        state.1.length state.2.length samples :=
  (bit_cost n rows hlen samples state havailable).2.trans
    (Nat.mul_le_mul_left _ (sourceTime_le n rows hlen samples state))

end Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
