import Counting.Algorithm.KarpLubyRequest.Sampling.TapeIterationSpec

/-!
# Length invariants along the actual sample and group orbits

The list specification is total on short tapes, but a successful physical
fair-tape call requires enough remaining bits. The lemmas below derive that
precondition at each visited state from one initial budget inequality. They also
bound the stored numerator words, without assigning unit cost to arithmetic.
Zero counts and zero width are included; no machine execution is assumed.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.TapeBounds
open Counting.Algorithm.KarpLuby
open TapeIterationSpec

variable {n : ℕ}

private theorem nat_word_length (a : ℕ) :
    (Computability.encodeNat a).length = a.size := Encoding.nat_length a

/-- Every untouched suffix is counted in addition to the remaining full blocks. -/
theorem drop_length (word : List Bool) (blocks width i : ℕ) (hi : i ≤ blocks)
    (hb : blocks * width ≤ word.length) :
    (word.drop (i * width)).length =
      (blocks - i) * width + (word.length - blocks * width) := by
  have hd : i * width + (blocks - i) * width = blocks * width := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hi]
  rw [List.length_drop]
  omega

theorem drop_available (word : List Bool) (blocks width i : ℕ) (hi : i < blocks)
    (hb : blocks * width ≤ word.length) :
    width ≤ (word.drop (i * width)).length := by
  have hs : i * width + width ≤ blocks * width := by
    calc
      _ = (i + 1) * width := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ _ := Nat.mul_le_mul_right width hi
  rw [List.length_drop]
  omega

theorem sample_tape_length (cs : List (DNF.Clause n)) (samples width i acc : ℕ)
    (word : List Bool) (hi : i ≤ samples) (hb : samples * width ≤ word.length) :
    ((sampleStep cs width)^[i] (acc, word)).2.length =
      (samples - i) * width + (word.length - samples * width) := by
  rw [sample_iterate_raw]
  exact drop_length word samples width i hi hb

theorem sample_tape_available (cs : List (DNF.Clause n)) (samples width i acc : ℕ)
    (word : List Bool) (hi : i < samples) (hb : samples * width ≤ word.length) :
    width ≤ ((sampleStep cs width)^[i] (acc, word)).2.length := by
  rw [sample_iterate_raw]
  exact drop_available word samples width i hi hb

/-- An exact initial suffix length is preserved at every sample-loop prefix. -/
theorem sample_tape_length_suffix (cs : List (DNF.Clause n))
    (samples width i acc : ℕ) (tape : CoinTape (samples * width))
    (suffix : List Bool) (hi : i ≤ samples) :
    ((sampleStep cs width)^[i] (acc, List.ofFn tape ++ suffix)).2.length =
      (samples - i) * width + suffix.length := by
  rw [sample_tape_length cs samples width i acc _ hi (by simp)]
  simp

theorem group_tape_length (cs : List (DNF.Clause n))
    (samples groups width j : ℕ) (pref : List ℕ) (word : List Bool)
    (hj : j ≤ groups) (hb : groups * (samples * width) ≤ word.length) :
    ((groupStep cs samples width)^[j] (pref, word)).2.length =
      (groups - j) * (samples * width) + (word.length - groups * (samples * width)) := by
  rw [group_iterate_raw]
  exact drop_length word groups (samples * width) j hj hb

theorem group_tape_available (cs : List (DNF.Clause n))
    (samples groups width j : ℕ) (pref : List ℕ) (word : List Bool)
    (hj : j < groups) (hb : groups * (samples * width) ≤ word.length) :
    samples * width ≤ ((groupStep cs samples width)^[j] (pref, word)).2.length := by
  rw [group_iterate_raw]
  exact drop_available word groups (samples * width) j hj hb

/-- The outer budget supplies the inner body's precondition at every visited pair. -/
theorem group_sample_available (cs : List (DNF.Clause n))
    (samples groups width j i : ℕ) (pref : List ℕ) (word : List Bool)
    (hj : j < groups) (hi : i < samples)
    (hb : groups * (samples * width) ≤ word.length) :
    width ≤ ((sampleStep cs width)^[i]
      (0, ((groupStep cs samples width)^[j] (pref, word)).2)).2.length := by
  exact sample_tape_available cs samples width i 0 _ hi
    (group_tape_available cs samples groups width j pref word hj hb)

theorem trial_le_two_pow (cs : List (DNF.Clause n)) (width r : ℕ)
    (hw : width = dyadicBits (Program.totalMass cs)) :
    Program.trial cs r ≤ 2 ^ width := by
  simpa only [dyadicSize, ← hw] using Program.trial_le_scale cs r

theorem sampleSum_le (cs : List (DNF.Clause n)) (width count : ℕ)
    (word : List Bool) (hw : width = dyadicBits (Program.totalMass cs)) :
    sampleSum cs width count word ≤ count * 2 ^ width := by
  have h := Cost.sum_le_length_mul_pow width
    ((List.range count).map fun i =>
      Program.trial cs (tapeValue ((word.drop (i * width)).take width))) (by
        intro a ha
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
        exact trial_le_two_pow cs width _ hw)
  simpa only [sampleSum, List.length_map, List.length_range] using h

theorem sampleSum_size_le (cs : List (DNF.Clause n)) (width count : ℕ)
    (word : List Bool) (hw : width = dyadicBits (Program.totalMass cs)) :
    (sampleSum cs width count word).size ≤ count.size + width + 1 := by
  have h := Cost.sum_size_le width
    ((List.range count).map fun i =>
      Program.trial cs (tapeValue ((word.drop (i * width)).take width))) (by
        intro a ha
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
        exact trial_le_two_pow cs width _ hw)
  simpa only [sampleSum, List.length_map, List.length_range] using h

theorem sampleSum_bits_le (cs : List (DNF.Clause n)) (width count : ℕ)
    (word : List Bool) (hw : width = dyadicBits (Program.totalMass cs)) :
    (Computability.encodeNat (sampleSum cs width count word)).length ≤
      (Computability.encodeNat count).length + width + 1 := by
  rw [nat_word_length, nat_word_length]
  exact sampleSum_size_le cs width count word hw

/-- Every partial accumulator is bounded by the full declared sample count. -/
theorem sample_accumulator_le (cs : List (DNF.Clause n)) (samples width i acc : ℕ)
    (word : List Bool) (hi : i ≤ samples)
    (hw : width = dyadicBits (Program.totalMass cs)) :
    ((sampleStep cs width)^[i] (acc, word)).1 ≤ acc + samples * 2 ^ width := by
  rw [sample_iterate_raw]
  exact Nat.add_le_add_left ((sampleSum_le cs width i word hw).trans
    (Nat.mul_le_mul_right _ hi)) acc

theorem sample_accumulator_bits_le (cs : List (DNF.Clause n)) (samples width i : ℕ)
    (word : List Bool) (hi : i ≤ samples)
    (hw : width = dyadicBits (Program.totalMass cs)) :
    (Computability.encodeNat ((sampleStep cs width)^[i] (0, word)).1).length ≤
      (Computability.encodeNat samples).length + width + 1 := by
  rw [sample_iterate_raw, Nat.zero_add, nat_word_length, nat_word_length]
  exact (sampleSum_size_le cs width i word hw).trans
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size hi) width) 1)

theorem group_prefix_length (cs : List (DNF.Clause n))
    (samples width count : ℕ) (pref : List ℕ) (word : List Bool) :
    ((groupStep cs samples width)^[count] (pref, word)).1.length =
      pref.length + count := by
  rw [group_iterate_raw]
  simp

/-- The same bound is retained by old numerators and every newly appended one. -/
theorem group_numerator_le (cs : List (DNF.Clause n))
    (samples width count : ℕ) (pref : List ℕ) (word : List Bool)
    (hw : width = dyadicBits (Program.totalMass cs))
    (hp : ∀ a ∈ pref, a ≤ samples * 2 ^ width) :
    ∀ a ∈ ((groupStep cs samples width)^[count] (pref, word)).1,
      a ≤ samples * 2 ^ width := by
  intro a ha
  rw [group_iterate_raw] at ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hp a ha
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    exact sampleSum_le cs width samples _ hw

theorem group_numerator_bits_le (cs : List (DNF.Clause n))
    (samples width count : ℕ) (pref : List ℕ) (word : List Bool)
    (hw : width = dyadicBits (Program.totalMass cs))
    (hp : ∀ a ∈ pref, (Computability.encodeNat a).length ≤
      (Computability.encodeNat samples).length + width + 1) :
    ∀ a ∈ ((groupStep cs samples width)^[count] (pref, word)).1,
      (Computability.encodeNat a).length ≤
        (Computability.encodeNat samples).length + width + 1 := by
  intro a ha
  rw [group_iterate_raw] at ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hp a ha
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    exact sampleSum_bits_le cs width samples _ hw

end Counting.Algorithm.KarpLubyRequest.Sampling.TapeBounds
