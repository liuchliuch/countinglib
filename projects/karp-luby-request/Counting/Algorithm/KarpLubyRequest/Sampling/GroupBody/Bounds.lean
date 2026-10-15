import Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Orbit

/-! # Uniform physical bounds for both nested real loops -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
open Turing Computability Holant.Complexity StackProtocol BinaryCompose GraphPreprocessing
open Counting.Algorithm.KarpLuby
open Counting.Algorithm.KarpLubyMachine
open TapeIterationSpec

theorem reversed_length_le (xs : List ℕ) (bits : ℕ)
    (h : ∀ a ∈ xs, (encodeNat a).length ≤ bits) :
    (GroupOutput.reversed xs).length ≤ xs.length * (2 * bits + 1) := by
  change (GroupOutput.body (xs.map encodeNat)).reverse.length ≤ _
  rw [List.length_reverse]
  induction xs with
  | nil => simp only [List.map_nil, GroupOutput.body_nil, List.length_nil, Nat.zero_mul, le_refl]
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp only [List.mem_cons]; exact Or.inr hb))
    simp only [List.map_cons, GroupOutput.body_cons, List.length_append,
      Encoding.frame_length, List.length_cons]
    nlinarith

theorem history_on_le (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (samples groups : ℕ)
    (tape : List Bool) (i : ℕ) (hi : i ≤ groups) :
    (((step (rows.map (DenseNormalization.denote n)) samples
      (encodeNat (TotalMass.rowSum rows)).length)^[i] (GroupOutput.reversed [], tape)).1).length ≤
      groups * (2 * (encodeNat samples).length + 2 * (encodeNat (TotalMass.rowSum rows)).length + 3) := by
  rw [iterate_view]
  have h := reversed_length_le
    (((groupStep (rows.map (DenseNormalization.denote n)) samples
      (encodeNat (TotalMass.rowSum rows)).length)^[i] ([], tape)).1)
    ((encodeNat samples).length + (encodeNat (TotalMass.rowSum rows)).length + 1)
    (TapeBounds.group_numerator_bits_le _ samples _ i [] tape
      (SampleBody.width_original n rows hlen) (by simp))
  rw [TapeBounds.group_prefix_length, List.length_nil, Nat.zero_add] at h
  have hm := Nat.mul_le_mul_right
    (2 * (encodeNat samples).length + 2 * (encodeNat (TotalMass.rowSum rows)).length + 3) hi
  nlinarith

theorem tape_on_le {n : ℕ} (cs : List (DNF.Clause n)) (samples width count : ℕ) (tape : List Bool) :
    (((step cs samples width)^[count] (GroupOutput.reversed [], tape)).2).length ≤ tape.length := by
  rw [iterate_view, group_iterate_raw]
  simp only [List.length_drop]
  omega

theorem timeBound_mono (rowLength width sampleBits samples h H t T : ℕ)
    (hh : h ≤ H) (ht : t ≤ T) :
    timeBound rowLength width sampleBits h t samples ≤
      timeBound rowLength width sampleBits H T samples := by
  unfold timeBound
  gcongr

theorem sourceTime_on_le (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (samples groups : ℕ)
    (tape : List Bool) (i : ℕ) (hi : i ≤ groups) :
    sourceTime n rows samples
      ((step (rows.map (DenseNormalization.denote n)) samples
        (encodeNat (TotalMass.rowSum rows)).length)^[i] (GroupOutput.reversed [], tape)) ≤
      timeBound (Dense.CellCodec.rows rows).length (encodeNat (TotalMass.rowSum rows)).length
        (encodeNat samples).length
        (groups * (2 * (encodeNat samples).length + 2 * (encodeNat (TotalMass.rowSum rows)).length + 3))
        tape.length samples :=
  (sourceTime_le n rows hlen samples _).trans
    (timeBound_mono _ _ _ _ _ _ _ _ (history_on_le n rows hlen samples groups tape i hi)
      (tape_on_le _ _ _ _ _))

def orbitWordBound (rowLength width sampleBits tapeLength groups : ℕ) : ℕ :=
  2 * rowLength + 2 * width + 2 * sampleBits +
    2 * (groups * (2 * sampleBits + 2 * width + 3)) + 4 + tapeLength

theorem state_word_on_le (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (samples groups : ℕ)
    (tape : List Bool) (i : ℕ) (hi : i ≤ groups) :
    ((stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)) (encodeNat samples)).encode
      ((step (rows.map (DenseNormalization.denote n)) samples
        (encodeNat (TotalMass.rowSum rows)).length)^[i] (GroupOutput.reversed [], tape))).length ≤
      orbitWordBound (Dense.CellCodec.rows rows).length (encodeNat (TotalMass.rowSum rows)).length
        (encodeNat samples).length tape.length groups := by
  rw [state_word_length]
  have hh := history_on_le n rows hlen samples groups tape i hi
  have ht := tape_on_le (rows.map (DenseNormalization.denote n)) samples
    (encodeNat (TotalMass.rowSum rows)).length i tape
  unfold orbitWordBound
  omega

/-- Complete measured cost of both nested finite-program loops. The remaining
pipeline substitutes its actual sample/group parameters into this expression. -/
theorem nested_bit_cost (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (samples groups : ℕ) (tape : List Bool)
    (havailable : groups * (samples * (encodeNat (TotalMass.rowSum rows)).length) ≤ tape.length) :
    let e := stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)) (encodeNat samples)
    let f := step (rows.map (DenseNormalization.denote n)) samples (encodeNat (TotalMass.rowSum rows)).length
    let B := timeBound (Dense.CellCodec.rows rows).length (encodeNat (TotalMass.rowSum rows)).length
      (encodeNat samples).length
      (groups * (2 * (encodeNat samples).length + 2 * (encodeNat (TotalMass.rowSum rows)).length + 3))
      tape.length samples
    let W := orbitWordBound (Dense.CellCodec.rows rows).length (encodeNat (TotalMass.rowSum rows)).length
      (encodeNat samples).length tape.length groups
    (Primitive.run (Iteration.program machine)
      (Iteration.ticks e f (sourceTime n rows samples) groups (GroupOutput.reversed [], tape))
      (some (cfg (Iteration.own machine 0) machine.initial
        (Iteration.ready machine (encodeNat groups) (e.encode (GroupOutput.reversed [], tape)))))).1 ≤
      (8 + machine.primitiveBudget) * (1 + groups * (B + 2 * (W + 1) + 2 * (encodeNat groups).length + 3)) := by
  dsimp only
  apply Iteration.bounded_bit_cost_on machine _ _ _ groups (GroupOutput.reversed [], tape)
    (source_on n rows hlen samples groups [] tape havailable)
  · intro i hi; exact sourceTime_on_le n rows hlen samples groups tape i (by omega)
  · intro i hi; exact state_word_on_le n rows hlen samples groups tape (i+1) (by omega)

end Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
