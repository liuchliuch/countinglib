import Counting.Algorithm.KarpLubyRequest.FairTape
import Counting.Algorithm.KarpLubyMachine.NumeratorMedian

/-!
# Physical tape slices and the original sample/group sums

The value equations use the most-significant-first fair-tape convention. The
sample and group loops retain an arbitrary unread suffix, including at zero
width or zero iteration count. No execution or cost witness is assumed here.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.TapeIterationSpec
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

/-- The positional value implemented by the existing fair-tape decoder. -/
def tapeValue (word : List Bool) : ℕ :=
  Holant.Complexity.BinaryArithmetic.value word.reverse

theorem tapeValue_ofFn (width : ℕ) (tape : CoinTape width) :
    tapeValue (List.ofFn tape) = Counting.Algorithm.KarpLuby.decodeNat width tape :=
  FairTape.value_ofFn width tape

/-- One trial consumes exactly the next declared-width block. -/
def sampleStep {n : ℕ} (cs : List (DNF.Clause n)) (width : ℕ)
    (state : ℕ × List Bool) : ℕ × List Bool :=
  (state.1 + Program.trial cs (tapeValue (state.2.take width)), state.2.drop width)

/-- A list expression for the same finite sequence of physical blocks. -/
def sampleSum {n : ℕ} (cs : List (DNF.Clause n)) (width count : ℕ)
    (word : List Bool) : ℕ :=
  ((List.range count).map fun i =>
    Program.trial cs (tapeValue ((word.drop (i * width)).take width))).sum

theorem sample_iterate_raw {n : ℕ} (cs : List (DNF.Clause n)) (width count acc : ℕ)
    (word : List Bool) :
    (sampleStep cs width)^[count] (acc, word) =
      (acc + sampleSum cs width count word, word.drop (count * width)) := by
  induction count with
  | zero => simp [sampleSum]
  | succ count ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [sampleStep, sampleSum, List.range_succ, List.map_append, List.sum_append,
      List.drop_drop, Nat.succ_mul, Nat.add_assoc]

theorem range_map_eq_ofFn {α : Type} (count : ℕ) (f : ℕ → α) :
    (List.range count).map f = List.ofFn (fun i : Fin count => f i.val) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp

/-- A literal take/drop block is the original row-major `coinChunk`.
Only indices inside the declared finite tape are inspected. -/
theorem chunk_word {blocks width : ℕ} (tape : CoinTape (blocks * width))
    (suffix : List Bool) (i : Fin blocks) :
    ((List.ofFn tape ++ suffix).drop (i.val * width)).take width =
      List.ofFn (Program.coinChunk (width := width) tape i) := by
  have hb : i.val * width + width ≤ blocks * width := by
    calc
      i.val * width + width = (i.val + 1) * width := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ blocks * width := Nat.mul_le_mul_right width i.isLt
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_append, List.length_ofFn]
    exact Nat.min_eq_left (by omega)
  · intro j hj hj'
    have hjw : j < width := by simpa only [List.length_ofFn] using hj'
    have hij : i.val * width + j < blocks * width := by omega
    rw [List.getElem_take, List.getElem_drop,
      List.getElem_append_left (by simpa only [List.length_ofFn] using hij),
      List.getElem_ofFn, List.getElem_ofFn]
    rfl

/-- The chunk and its literal unread suffix reconstruct the dropped tape. -/
theorem drop_eq_chunk_append {blocks width : ℕ} (tape : CoinTape (blocks * width))
    (suffix : List Bool) (i : Fin blocks) :
    (List.ofFn tape ++ suffix).drop (i.val * width) =
      List.ofFn (Program.coinChunk (width := width) tape i) ++
        ((List.ofFn tape ++ suffix).drop (i.val * width)).drop width := by
  have h := List.take_append_drop width ((List.ofFn tape ++ suffix).drop (i.val * width))
  rw [chunk_word tape suffix i] at h
  exact h.symm

theorem drop_ofFn_suffix {size : ℕ} (tape : CoinTape size) (suffix : List Bool) :
    (List.ofFn tape ++ suffix).drop size = suffix := by
  exact List.drop_left' (by simp)

theorem sampleSum_ofFn {n : ℕ} (cs : List (DNF.Clause n)) (samples width : ℕ)
    (tape : CoinTape (samples * width)) (suffix : List Bool) :
    sampleSum cs width samples (List.ofFn tape ++ suffix) =
      (NumeratorMedian.groupNumeratorWithWidth cs samples width tape).value := by
  rw [sampleSum, range_map_eq_ofFn, NumeratorMedian.groupNumeratorWithWidth_value]
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [chunk_word tape suffix i, tapeValue_ofFn]

/-- Repeated sample steps produce the original group numerator and preserve
every bit after its declared tape, for all sample counts and widths. -/
theorem sample_iterate {n : ℕ} (cs : List (DNF.Clause n)) (samples width acc : ℕ)
    (tape : CoinTape (samples * width)) (suffix : List Bool) :
    (sampleStep cs width)^[samples] (acc, List.ofFn tape ++ suffix) =
      (acc + (NumeratorMedian.groupNumeratorWithWidth cs samples width tape).value,
        suffix) := by
  rw [sample_iterate_raw, sampleSum_ofFn, drop_ofFn_suffix]

/-- One group starts a fresh numerator and appends its value in source order. -/
def groupStep {n : ℕ} (cs : List (DNF.Clause n)) (samples width : ℕ)
    (state : List ℕ × List Bool) : List ℕ × List Bool :=
  let result := (sampleStep cs width)^[samples] (0, state.2)
  (state.1 ++ [result.1], result.2)

theorem groupStep_eq {n : ℕ} (cs : List (DNF.Clause n)) (samples width : ℕ)
    (groups : List ℕ) (word : List Bool) :
    groupStep cs samples width (groups, word) =
      (groups ++ [sampleSum cs width samples word], word.drop (samples * width)) := by
  simp only [groupStep, sample_iterate_raw, Nat.zero_add]

theorem group_iterate_raw {n : ℕ} (cs : List (DNF.Clause n))
    (samples width count : ℕ) (groups : List ℕ) (word : List Bool) :
    (groupStep cs samples width)^[count] (groups, word) =
      (groups ++ (List.range count).map (fun i =>
        sampleSum cs width samples (word.drop (i * (samples * width)))),
        word.drop (count * (samples * width))) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [Function.iterate_succ_apply', ih, groupStep_eq]
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.drop_drop, Nat.succ_mul]

/-- All physically materialized group numerators agree with the original
finite family in its original order. Zero-width groups still append a result. -/
theorem group_iterate {n : ℕ} (cs : List (DNF.Clause n))
    (samples width count : ℕ) (groups : List ℕ)
    (tape : CoinTape (count * (samples * width))) (suffix : List Bool) :
    (groupStep cs samples width)^[count] (groups, List.ofFn tape ++ suffix) =
      (groups ++ List.ofFn (fun i : Fin count =>
        (NumeratorMedian.groupNumeratorWithWidth cs samples width
          (Program.coinChunk (width := samples * width) tape i)).value), suffix) := by
  rw [group_iterate_raw, drop_ofFn_suffix, range_map_eq_ofFn]
  congr 1
  apply congrArg (List.append groups)
  apply congrArg List.ofFn
  funext i
  rw [drop_eq_chunk_append tape suffix i, sampleSum_ofFn]

end Counting.Algorithm.KarpLubyRequest.Sampling.TapeIterationSpec
