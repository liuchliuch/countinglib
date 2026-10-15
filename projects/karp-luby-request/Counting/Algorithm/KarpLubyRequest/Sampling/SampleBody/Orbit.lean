import Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody.Bounds
import Counting.Algorithm.KarpLubyRequest.Sampling.TapeBounds
import Counting.Algorithm.KarpLubyRequest.Iteration.Orbit

/-! # Actual sample-body runs at every visited state of a bounded tape -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine
open TapeIterationSpec

set_option backward.isDefEq.respectTransparency false

theorem width_original (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) :
    (encodeNat (TotalMass.rowSum rows)).length =
      dyadicBits (Program.totalMass (rows.map (DenseNormalization.denote n))) := by
  change (Encoding.nat.encode (TotalMass.rowSum rows)).length = _
  rw [Encoding.nat_length, TotalMass.rowSum_original n rows hlen]
  rfl

/-- One initial physical tape inequality supplies every actual body call. -/
theorem source_on (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (samples acc : ℕ) (tape : List Bool)
    (havailable : samples * (encodeNat (TotalMass.rowSum rows)).length ≤ tape.length)
    (i : ℕ) (hi : i < samples) :
    let e := stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
    let f := sampleStep (rows.map (DenseNormalization.denote n)) (encodeNat (TotalMass.rowSum rows)).length
    Iteration.SourceRun machine (e.encode (f^[i] (acc, tape)))
      (e.encode (f (f^[i] (acc, tape)))) (sourceTime n rows (f^[i] (acc, tape))) := by
  apply source_run n rows hlen
  exact TapeBounds.sample_tape_available _ samples _ i acc tape hi havailable

/-- The complete real countdown loop materializes the original ordered sum
and retains its literal suffix. This also covers zero samples and zero width. -/
theorem sample_loop (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (samples acc : ℕ) (tape : List Bool)
    (havailable : samples * (encodeNat (TotalMass.rowSum rows)).length ≤ tape.length) :
    let e := stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
    let f := sampleStep (rows.map (DenseNormalization.denote n)) (encodeNat (TotalMass.rowSum rows)).length
    RunsExactly (Iteration.computer machine).step
      (cfg (Iteration.own machine 0) machine.initial
        (Iteration.ready machine (encodeNat samples) (e.encode (acc, tape))))
      (Iteration.finished machine
        (e.encode (acc + sampleSum (rows.map (DenseNormalization.denote n))
          (encodeNat (TotalMass.rowSum rows)).length samples tape,
            tape.drop (samples * (encodeNat (TotalMass.rowSum rows)).length))))
      (Iteration.ticks e f (sourceTime n rows) samples (acc, tape)) := by
  dsimp only
  have h := Iteration.run_on machine
    (stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)))
    (sampleStep (rows.map (DenseNormalization.denote n)) (encodeNat (TotalMass.rowSum rows)).length)
    (sourceTime n rows) samples (acc, tape) (source_on n rows hlen samples acc tape havailable)
  rw [sample_iterate_raw] at h
  exact h

/-- A uniform body-time bound along a sample group, starting at accumulator zero. -/
theorem sourceTime_on_le (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (samples : ℕ) (tape : List Bool)
    (i : ℕ) (hi : i ≤ samples) :
    sourceTime n rows
      ((sampleStep (rows.map (DenseNormalization.denote n))
        (encodeNat (TotalMass.rowSum rows)).length)^[i] (0, tape)) ≤
      220 * ((Dense.CellCodec.rows rows).length + 2 * (encodeNat (TotalMass.rowSum rows)).length + 1)^2 +
        4 * (Dense.CellCodec.rows rows).length + 14 * (encodeNat (TotalMass.rowSum rows)).length +
          6 * (encodeNat samples).length + 31 := by
  have ht := sourceTime_le n rows hlen
    ((sampleStep (rows.map (DenseNormalization.denote n))
      (encodeNat (TotalMass.rowSum rows)).length)^[i] (0, tape))
  have ha := TapeBounds.sample_accumulator_bits_le
    (rows.map (DenseNormalization.denote n)) samples (encodeNat (TotalMass.rowSum rows)).length
    i tape hi (width_original n rows hlen)
  omega

/-- Serialized words along the loop count the entire remaining tape as storage. -/
theorem state_word_on_le (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (samples : ℕ) (tape : List Bool)
    (i : ℕ) (hi : i ≤ samples) :
    ((stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))).encode
      ((sampleStep (rows.map (DenseNormalization.denote n))
        (encodeNat (TotalMass.rowSum rows)).length)^[i] (0, tape))).length ≤
      2 * (Dense.CellCodec.rows rows).length + 4 * (encodeNat (TotalMass.rowSum rows)).length +
        2 * (encodeNat samples).length + 5 + tape.length := by
  have ha := TapeBounds.sample_accumulator_bits_le
    (rows.map (DenseNormalization.denote n)) samples (encodeNat (TotalMass.rowSum rows)).length
    i tape hi (width_original n rows hlen)
  change (word _ _ _ _).length ≤ _
  rw [word_length]
  rw [sample_iterate_raw] at ha ⊢
  simp only [Nat.zero_add, List.length_drop] at ha ⊢
  omega

end Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
