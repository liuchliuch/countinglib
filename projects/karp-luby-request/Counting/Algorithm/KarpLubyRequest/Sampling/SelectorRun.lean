import Counting.Algorithm.KarpLubyRequest.Sampling.SelectorAdvance
import Counting.Algorithm.KarpLubyRequest.Sampling.SelectorSpec

/-! # Complete finite interval-selection execution and physical input bounds -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Selector
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby

def resultCfg (r : SelectorSpec.Result) : Cfg Stack Label Memory :=
  finished r.selected (Dense.CellCodec.rows r.remaining) (encodeNat r.rank)
    (Dense.CellCodec.encode r.row)
    (if r.selected then encodeNat (2 ^ RowSemantics.free r.row) else [])
    (Dense.CellCodec.rows r.prior)

def runTime : List RowSemantics.Cells → ℕ → ℕ
  | [], _ => 1
  | row :: rest, r =>
      if r < 2 ^ RowSemantics.free row then compareTime row r + 1
      else runTime rest (r - 2 ^ RowSemantics.free row) + advanceTime row r + compareTime row r

/-- The stored result includes the residual rank and reversed occurrence history;
the finite program never carries an unbounded selected index in its state. -/
theorem run_exact (rows : List RowSemantics.Cells) (r : ℕ) (prior : List RowSemantics.Cells) :
    RunsExactly computer.step
      (config 0 (Dense.CellCodec.rows rows) (encodeNat r) [] [] [] [] [] [] []
        (Dense.CellCodec.rows prior) [])
      (resultCfg (SelectorSpec.seek rows r prior)) (runTime rows r) := by
  induction rows generalizing r prior with
  | nil =>
    simpa only [runTime, SelectorSpec.seek, resultCfg, Dense.CellCodec.rows_nil,
      Dense.CellCodec.encode_nil, Bool.false_eq_true, ↓reduceIte] using
      runsExactly_one (empty_step (encodeNat r) (Dense.CellCodec.rows prior))
  | cons row rest ih =>
    have hc := compare_row row r (Dense.CellCodec.rows rest) (Dense.CellCodec.rows prior)
    by_cases h : r < 2 ^ RowSemantics.free row
    · have hs := selected_step (Dense.CellCodec.rows rest) (encodeNat r)
        (Dense.CellCodec.encode row) (encodeNat (2 ^ RowSemantics.free row))
        (Dense.CellCodec.rows prior)
      simp only [h, decide_true] at hc
      simpa only [runTime, SelectorSpec.seek, if_pos h, resultCfg, ↓reduceIte,
        Dense.CellCodec.rows_cons, Nat.add_comm] using hc.trans (runsExactly_one hs)
    · have ha := advance_row row r (Dense.CellCodec.rows rest) (Dense.CellCodec.rows prior)
      simp only [h, decide_false] at hc
      have hn := ih (r - 2 ^ RowSemantics.free row) (row :: prior)
      simp only [Dense.CellCodec.rows_cons] at hn
      simpa only [runTime, SelectorSpec.seek, if_neg h, Dense.CellCodec.rows_cons,
        Nat.add_assoc] using (hc.trans ha).trans hn

theorem residual_length (r mass : ℕ) :
    (encodeNat (r - mass)).length ≤ (encodeNat r).length := by
  change (Encoding.nat.encode (r - mass)).length ≤ (Encoding.nat.encode r).length
  rw [Encoding.nat_length, Encoding.nat_length]
  exact Nat.size_le_size (Nat.sub_le r mass)

def capacity (rows : List RowSemantics.Cells) (r : ℕ) : ℕ :=
  (Dense.CellCodec.rows rows).length + (encodeNat r).length + 1

theorem capacity_next (row : RowSemantics.Cells) (rest : List RowSemantics.Cells) (r : ℕ) :
    capacity rest (r - 2 ^ RowSemantics.free row) ≤ capacity (row :: rest) r := by
  have hr := residual_length r (2 ^ RowSemantics.free row)
  simp only [capacity, Dense.CellCodec.rows_cons, List.length_append,
    Encoding.frame_length, Dense.CellCodec.encode_length]
  omega

theorem iteration_bound (row : RowSemantics.Cells) (rest : List RowSemantics.Cells) (r : ℕ) :
    compareTime row r + advanceTime row r + 1 ≤ 30 * capacity (row :: rest) r := by
  have hm := TotalMass.mass_length row
  have hr := residual_length r (2 ^ RowSemantics.free row)
  simp only [compareTime, advanceTime, capacity, Dense.CellCodec.rows_cons,
    List.length_append, Encoding.frame_length, Dense.CellCodec.encode_length]
  omega

theorem time_bound (rows : List RowSemantics.Cells) (r : ℕ) :
    runTime rows r ≤ 30 * (rows.length + 1) * capacity rows r := by
  induction rows generalizing r with
  | nil => simp only [runTime, List.length_nil, Nat.zero_add, Nat.mul_one, capacity,
      Dense.CellCodec.rows_nil, List.length_nil, Nat.zero_add]; omega
  | cons row rest ih =>
    have ht := ih (r - 2 ^ RowSemantics.free row)
    have hc := capacity_next row rest r
    have hr := iteration_bound row rest r
    have hm := Nat.mul_le_mul_left (30 * (rest.length + 1)) hc
    simp only [runTime, List.length_cons]
    split_ifs <;> nlinarith

/-- Input size here is the physically stored row stream plus the canonical rank.
An existing history suffix is never scanned by this routine. -/
theorem input_time_bound (rows : List RowSemantics.Cells) (r : ℕ) :
    runTime rows r ≤ 30 * ((Dense.CellCodec.rows rows).length + (encodeNat r).length + 1)^2 := by
  have ht := time_bound rows r
  have hn := TotalMass.count_le_input rows
  have hm := Nat.mul_le_mul_right (capacity rows r)
    (Nat.mul_le_mul_left 30 (show rows.length + 1 ≤ capacity rows r by dsimp [capacity]; omega))
  dsimp only [capacity] at ht hm
  nlinarith

theorem primitive_cost (rows : List RowSemantics.Cells) (r : ℕ) (prior : List RowSemantics.Cells) :
    (Primitive.run program (runTime rows r)
      (some (config 0 (Dense.CellCodec.rows rows) (encodeNat r) [] [] [] [] [] [] []
        (Dense.CellCodec.rows prior) []))).2 = some (resultCfg (SelectorSpec.seek rows r prior)) ∧
    (Primitive.run program (runTime rows r)
      (some (config 0 (Dense.CellCodec.rows rows) (encodeNat r) [] [] [] [] [] [] []
        (Dense.CellCodec.rows prior) []))).1 ≤
      240 * ((Dense.CellCodec.rows rows).length + (encodeNat r).length + 1)^2 := by
  have h := Primitive.execution_cost program 8 statement_budget _ _ _ (run_exact rows r prior)
  refine ⟨h.1, h.2.trans ?_⟩
  have ht := input_time_bound rows r
  nlinarith

end Counting.Algorithm.KarpLubyRequest.Sampling.Selector
