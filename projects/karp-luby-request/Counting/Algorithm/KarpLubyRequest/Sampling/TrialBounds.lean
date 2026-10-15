import Counting.Algorithm.KarpLubyRequest.Sampling.TrialFlow
import Holant.Complexity.BinaryArithmetic.SubtractBits

/-!
# Physical input bounds for the connected one-trial execution

The charged time is the actual selector, unranker, owner scan, scale constructor
and fourteen cleanup loops from `TrialFlow`. The untouched random suffix is not
scanned and does not occur in the bound. The mass word may be arbitrary here;
the original-estimator value theorem imposes its canonical mass separately.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.TrialBounds
open Counting.Algorithm.KarpLuby
open Computability

theorem seek_rank_le (rows : List RowSemantics.Cells) (r : ℕ)
    (prior : List RowSemantics.Cells) :
    (SelectorSpec.seek rows r prior).rank ≤ r := by
  induction rows generalizing r prior with
  | nil => exact Nat.le_refl _
  | cons row rest ih =>
    simp only [SelectorSpec.seek]
    split_ifs
    · exact Nat.le_refl _
    · exact (ih (r - 2 ^ RowSemantics.free row) (row :: prior)).trans (Nat.sub_le _ _)

theorem seek_rank_length_le (rows : List RowSemantics.Cells) (r : ℕ)
    (prior : List RowSemantics.Cells) :
    (encodeNat (SelectorSpec.seek rows r prior).rank).length ≤ (encodeNat r).length := by
  change (Encoding.nat.encode _).length ≤ (Encoding.nat.encode _).length
  rw [Encoding.nat_length, Encoding.nat_length]
  exact Nat.size_le_size (seek_rank_le rows r prior)

/-- Skipped occurrences move to history; the selected row's storage is charged
to its original frame. This includes failed selection and empty rows. -/
theorem seek_physical_bound (rows : List RowSemantics.Cells) (r : ℕ)
    (prior : List RowSemantics.Cells) :
    (Dense.CellCodec.rows (SelectorSpec.seek rows r prior).remaining).length +
      (Dense.CellCodec.rows (SelectorSpec.seek rows r prior).prior).length +
        2 * (SelectorSpec.seek rows r prior).row.length ≤
      (Dense.CellCodec.rows rows).length + (Dense.CellCodec.rows prior).length := by
  induction rows generalizing r prior with
  | nil => simp [SelectorSpec.seek]
  | cons row rest ih =>
    by_cases h : r < 2 ^ RowSemantics.free row
    · simp only [SelectorSpec.seek, if_pos h, Dense.CellCodec.rows_cons,
        List.length_append, Encoding.frame_length, Dense.CellCodec.encode_length]
      omega
    · have ht := ih (r - 2 ^ RowSemantics.free row) (row :: prior)
      simp only [Dense.CellCodec.rows_cons, List.length_append, Encoding.frame_length,
        Dense.CellCodec.encode_length] at ht
      simp only [SelectorSpec.seek, if_neg h, Dense.CellCodec.rows_cons,
        List.length_append, Encoding.frame_length, Dense.CellCodec.encode_length]
      omega

theorem owner_remaining_length_le (rows : List RowSemantics.Cells) (assignment : List Bool) :
    (Dense.CellCodec.rows (Owner.remaining rows assignment)).length ≤
      (Dense.CellCodec.rows rows).length := by
  induction rows with
  | nil => exact Nat.le_refl _
  | cons row rest ih =>
    simp only [Owner.remaining, Dense.CellCodec.rows_cons, List.length_append]
    split_ifs <;> omega

theorem result_mass_length (q : SelectorSpec.Result) :
    (if q.selected then encodeNat (2 ^ RowSemantics.free q.row) else []).length ≤
      q.row.length + 1 := by
  cases hs : q.selected
  · simp [hs]
  · simpa only [hs, ↓reduceIte] using TotalMass.mass_length q.row

theorem cleanup_selected_bound (rows mass suffix : List Bool) (q : SelectorSpec.Result)
    (L R : ℕ) (hr : (encodeNat q.rank).length ≤ R)
    (hq : (Dense.CellCodec.rows q.remaining).length +
      (Dense.CellCodec.rows q.prior).length + 2 * q.row.length ≤ L) :
    Trial.cleanupTime (Trial.selectedData rows mass suffix q) ≤ R + 2 * L + 16 := by
  have hm := result_mass_length q
  simp only [Trial.cleanupTime, Trial.selectedData, Trial.inputData,
    List.length_nil, Nat.add_zero, Dense.CellCodec.encode_length]
  omega

theorem cleanup_owned_bound (rows mass suffix : List Bool) (q : SelectorSpec.Result)
    (L R : ℕ) (hr : (encodeNat q.rank).length ≤ R)
    (hq : (Dense.CellCodec.rows q.remaining).length +
      (Dense.CellCodec.rows q.prior).length + 2 * q.row.length ≤ L) :
    Trial.cleanupTime (Trial.ownedData rows mass suffix q) ≤ R + L + 16 := by
  have hm := result_mass_length q
  have hh := owner_remaining_length_le q.prior (RowSemantics.sample q.row q.rank)
  simp only [Trial.cleanupTime, Trial.ownedData, Trial.sampledData, Trial.selectedData,
    Trial.inputData, List.length_nil, Nat.add_zero, RowSemantics.sample_length,
    List.length_drop]
  omega

theorem cleanup_scaled_eq (rows mass suffix : List Bool) (q : SelectorSpec.Result) :
    Trial.cleanupTime (Trial.scaledData rows mass suffix q) =
      Trial.cleanupTime (Trial.ownedData rows mass suffix q) := rfl

/-- The post-selection bound includes both success and early-rejection cleanup. -/
theorem after_time_bound (rows mass suffix : List Bool) (q : SelectorSpec.Result)
    (L R : ℕ) (hr : (encodeNat q.rank).length ≤ R)
    (hq : (Dense.CellCodec.rows q.remaining).length +
      (Dense.CellCodec.rows q.prior).length + 2 * q.row.length ≤ L)
    (hlen : q.selected = true → ∀ row ∈ q.prior, row.length = q.row.length) :
    Trial.afterTime rows mass suffix q ≤ 40 * (L + mass.length + R + 1)^2 := by
  have hc := cleanup_selected_bound rows mass suffix q L R hr hq
  have ho := cleanup_owned_bound rows mass suffix q L R hr hq
  have hs : Trial.cleanupTime (Trial.scaledData rows mass suffix q) ≤ R + L + 16 := by
    rw [cleanup_scaled_eq]
    exact ho
  have hn : 1 ≤ L + mass.length + R + 1 := by omega
  have hsq : L + mass.length + R + 1 ≤ (L + mass.length + R + 1)^2 := by
    nlinarith [Nat.mul_le_mul_left (L + mass.length + R + 1) hn]
  cases hb : q.selected with
  | false =>
    simp only [Trial.afterTime, hb, Bool.false_eq_true, ↓reduceIte]
    nlinarith
  | true =>
    have ht := Owner.input_time_bound q.prior (RowSemantics.sample q.row q.rank)
      (by simpa only [RowSemantics.sample_length] using hlen hb)
    simp only [RowSemantics.sample_length] at ht
    have ht' : Owner.runTime q.prior (RowSemantics.sample q.row q.rank) ≤
        8 * (L + mass.length + R + 1)^2 := by
      refine ht.trans ?_
      exact Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (by omega) 2)
    simp only [Trial.afterTime, hb, ↓reduceIte]
    split_ifs <;> nlinarith

/-- A quadratic bound for the same complete selector-to-halt source execution. -/
theorem selected_time_bound (n : ℕ) (rows : List RowSemantics.Cells)
    (mass suffix : List Bool) (r : ℕ) (hlen : ∀ row ∈ rows, row.length = n) :
    Trial.selectedTime rows mass suffix r ≤
      200 * ((Dense.CellCodec.rows rows).length + mass.length + (encodeNat r).length + 1)^2 := by
  have hq := seek_physical_bound rows r []
  simp only [Dense.CellCodec.rows_nil, List.length_nil, Nat.add_zero] at hq
  have hr := seek_rank_length_le rows r []
  have ha := after_time_bound (Dense.CellCodec.rows rows) mass suffix
    (SelectorSpec.seek rows r []) (Dense.CellCodec.rows rows).length (encodeNat r).length
    hr hq (by
      intro hs row hm
      have hp := TrialSpec.selected_prior_length n rows r hlen hs row hm
      have hrow := SelectorSpec.selected_row_length n rows r [] hlen hs
      exact hp.trans hrow.symm)
  have ht : Selector.runTime rows r ≤
      30 * ((Dense.CellCodec.rows rows).length + mass.length + (encodeNat r).length + 1)^2 := by
    refine (Selector.input_time_bound rows r).trans ?_
    gcongr
    omega
  unfold Trial.selectedTime
  nlinarith

/-- Adding the physically scanned mass-clock and row-copy prefix remains quadratic.
The prefix's execution equality is established by the separate random-stage source. -/
theorem prefix_selected_time_bound (n : ℕ) (rows : List RowSemantics.Cells)
    (mass suffix : List Bool) (r : ℕ) (hlen : ∀ row ∈ rows, row.length = n) :
    3 * mass.length + 2 * (Dense.CellCodec.rows rows).length + 6 +
      Trial.selectedTime rows mass suffix r ≤
        220 * ((Dense.CellCodec.rows rows).length + mass.length + (encodeNat r).length + 1)^2 := by
  have ht := selected_time_bound n rows mass suffix r hlen
  have hn : 1 ≤ (Dense.CellCodec.rows rows).length + mass.length + (encodeNat r).length + 1 := by omega
  have hsq : (Dense.CellCodec.rows rows).length + mass.length + (encodeNat r).length + 1 ≤
      ((Dense.CellCodec.rows rows).length + mass.length + (encodeNat r).length + 1)^2 := by
    nlinarith [Nat.mul_le_mul_left
      ((Dense.CellCodec.rows rows).length + mass.length + (encodeNat r).length + 1) hn]
  nlinarith

/-- Positional fair bits normalize to a canonical rank of at most their width.
This is a value/length fact even on a short word, not a successful-read theorem. -/
theorem fair_rank_length_le (word : List Bool) (width : ℕ) :
    (encodeNat (Holant.Complexity.BinaryArithmetic.value
      (word.take width).reverse)).length ≤ width := by
  change (Encoding.nat.encode _).length ≤ width
  rw [Encoding.nat_length]
  have hv := Nat.size_le.mpr
    (Holant.Complexity.BinaryArithmetic.value_lt_pow_length (word.take width).reverse)
  have hl : (word.take width).reverse.length ≤ width := by
    simp only [List.length_reverse, List.length_take]
    exact Nat.min_le_left _ _
  exact hv.trans hl

/-- Substitute the actual fair-bit rank into the connected prefix/time expression.
The read-length premise is retained for its intended successful caller. -/
theorem fair_prefix_time_bound (n : ℕ) (rows : List RowSemantics.Cells)
    (mass random : List Bool) (hlen : ∀ row ∈ rows, row.length = n)
    (_hbits : mass.length ≤ random.length) :
    3 * mass.length + 2 * (Dense.CellCodec.rows rows).length + 6 +
      Trial.selectedTime rows mass (random.drop mass.length)
        (Holant.Complexity.BinaryArithmetic.value (random.take mass.length).reverse) ≤
      220 * ((Dense.CellCodec.rows rows).length + 2 * mass.length + 1)^2 := by
  have hr := fair_rank_length_le random mass.length
  refine (prefix_selected_time_bound n rows mass (random.drop mass.length) _ hlen).trans ?_
  exact Nat.mul_le_mul_left 220 (Nat.pow_le_pow_left (by omega) 2)

end Counting.Algorithm.KarpLubyRequest.Sampling.TrialBounds
