import Counting.Algorithm.KarpLubyRequest.Sampling.TotalMassStages

/-!
# Complete list execution and polynomial cost of mass preprocessing

The induction follows the actual framed-row loop. Binary widths grow by at most
the physical size charged to each remaining row; the proof never uses a loop
bound proportional to an exponential clause cardinality.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.TotalMass
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby

def rowSum (xs : List RowSemantics.Cells) : ℕ := (xs.map (fun row => 2 ^ RowSemantics.free row)).sum
def workSize (xs : List RowSemantics.Cells) : ℕ := (xs.map (fun row => row.length + 2)).sum
def capacity (xs : List RowSemantics.Cells) (a : ℕ) : ℕ := (encodeNat a).length + workSize xs

def runTime : List RowSemantics.Cells → ℕ → ℕ
  | [], _ => 1
  | row :: xs, a => runTime xs (a + 2 ^ RowSemantics.free row) + rowTime row a

/-- Equal-length stored rows denote the original tagged clause union, retaining
every repeated occurrence and every explicit ambient coordinate. -/
theorem rowSum_original (n : ℕ) (xs : List RowSemantics.Cells)
    (hlen : ∀ row ∈ xs, row.length = n) :
    rowSum xs = Program.totalMass (xs.map (Counting.Algorithm.KarpLubyMachine.DenseNormalization.denote n)) := by
  induction xs with
  | nil => rfl
  | cons row xs ih =>
    have hr := hlen row (by simp)
    have ht := ih (fun row hm => hlen row (by simp [hm]))
    have hm : 2 ^ RowSemantics.free row = DNF.clauseMass
        (Counting.Algorithm.KarpLubyMachine.DenseNormalization.denote n row) := by
      subst n
      dsimp only [DNF.clauseMass]
      rw [RowSemantics.free_denote]
    simp only [rowSum, List.map_cons, List.sum_cons, Program.totalMass_cons] at *
    rw [hm, ht]

theorem run_exact (xs : List RowSemantics.Cells) (a : ℕ) :
    RunsExactly computer.step (config 0 (Dense.CellCodec.rows xs) [] (encodeNat a) [] [] [])
      (finished (encodeNat (a + rowSum xs))) (runTime xs a) := by
  induction xs generalizing a with
  | nil => simpa only [Dense.CellCodec.rows_nil, rowSum, List.map_nil, List.sum_nil,
      Nat.add_zero, runTime] using runsExactly_one (loop_empty (encodeNat a))
  | cons row xs ih =>
    have hr := (row_iteration row (Dense.CellCodec.rows xs) a).trans (ih (a + 2 ^ RowSemantics.free row))
    simpa only [Dense.CellCodec.rows_cons, rowSum, List.map_cons, List.sum_cons,
      runTime, Nat.add_assoc] using hr

theorem mass_length (row : RowSemantics.Cells) :
    (encodeNat (2 ^ RowSemantics.free row)).length ≤ row.length + 1 := by
  rw [← RowMass.power_word, List.length_append, List.length_replicate]
  have hf := RowSemantics.free_le row
  simpa using Nat.add_le_add_right hf 1

theorem addition_length (a b : ℕ) :
    (encodeNat (a + b)).length ≤ (encodeNat a).length + (encodeNat b).length + 1 := by
  have h := BinaryArithmetic.addBits_length_le false (encodeNat a) (encodeNat b)
  rw [BinaryArithmetic.addBits_encodeNat] at h
  omega

theorem capacity_next (row : RowSemantics.Cells) (xs : List RowSemantics.Cells) (a : ℕ) :
    capacity xs (a + 2 ^ RowSemantics.free row) ≤ capacity (row :: xs) a := by
  have ha := addition_length a (2 ^ RowSemantics.free row)
  have hm := mass_length row
  simp only [capacity, workSize, List.map_cons, List.sum_cons]
  omega

theorem rowTime_bound (row : RowSemantics.Cells) (xs : List RowSemantics.Cells) (a : ℕ) :
    rowTime row a ≤ 10 * (capacity (row :: xs) a + 1) := by
  have ha := addition_length a (2 ^ RowSemantics.free row)
  have hm := mass_length row
  simp only [rowTime, capacity, workSize, List.map_cons, List.sum_cons]
  omega

/-- The bound charges each physical iteration, using a nonincreasing width budget. -/
theorem time_bound (xs : List RowSemantics.Cells) (a : ℕ) :
    runTime xs a ≤ 10 * (xs.length + 1) * (capacity xs a + 1) := by
  induction xs generalizing a with
  | nil => simp only [runTime, List.length_nil, Nat.zero_add, Nat.mul_one]; omega
  | cons row xs ih =>
    have ht := ih (a + 2 ^ RowSemantics.free row)
    have hc := capacity_next row xs a
    have hr := rowTime_bound row xs a
    have hm := Nat.mul_le_mul_left (10 * (xs.length + 1)) (Nat.add_le_add_right hc 1)
    simp only [runTime, List.length_cons]
    nlinarith

theorem count_le_input (xs : List RowSemantics.Cells) : xs.length ≤ (Dense.CellCodec.rows xs).length := by
  induction xs with
  | nil => simp
  | cons row xs ih =>
    simp only [List.length_cons, Dense.CellCodec.rows_cons, List.length_append,
      Encoding.frame_length, Dense.CellCodec.encode_length]
    omega

theorem workSize_le_input (xs : List RowSemantics.Cells) :
    workSize xs ≤ 2 * (Dense.CellCodec.rows xs).length := by
  induction xs with
  | nil => rfl
  | cons row xs ih =>
    simp only [workSize, List.map_cons, List.sum_cons, Dense.CellCodec.rows_cons,
      List.length_append, Encoding.frame_length, Dense.CellCodec.encode_length] at *
    omega

/-- Full transition bound in the physical serialized row-list length. -/
theorem input_time_bound (xs : List RowSemantics.Cells) :
    runTime xs 0 ≤ 20 * ((Dense.CellCodec.rows xs).length + 1) ^ 2 := by
  have ht := time_bound xs 0
  have hn := count_le_input xs
  have hw := workSize_le_input xs
  have hz : encodeNat 0 = [] := rfl
  rw [capacity, hz, List.length_nil, Nat.zero_add] at ht
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 10 (Nat.add_le_add_right hn 1))
    (Nat.add_le_add_right hw 1)
  nlinarith

theorem init_eq (word : List Bool) :
    initList computer word = config 0 word [] [] [] [] [] := by
  dsimp only [initList, config, cfg]
  congr 1
  funext k; fin_cases k <;> rfl

theorem halt_eq (word : List Bool) : haltList computer word = finished word := by
  dsimp only [haltList, finished]
  congr 1
  funext k; fin_cases k <;> rfl

/-- The complete mass routine has a clean single-input/single-output contract. -/
theorem clean_run (xs : List RowSemantics.Cells) :
    RunsExactly computer.step (initList computer (Dense.CellCodec.rows xs))
      (haltList computer (encodeNat (rowSum xs))) (runTime xs 0) := by
  have hz : encodeNat 0 = [] := rfl
  simpa only [init_eq, halt_eq, hz, Nat.zero_add] using run_exact xs 0

theorem primitive_cost (xs : List RowSemantics.Cells) :
    (Primitive.run program (runTime xs 0) (some (initList computer (Dense.CellCodec.rows xs)))).2 =
      some (haltList computer (encodeNat (rowSum xs))) ∧
    (Primitive.run program (runTime xs 0) (some (initList computer (Dense.CellCodec.rows xs)))).1 ≤
      160 * ((Dense.CellCodec.rows xs).length + 1) ^ 2 := by
  have h := Primitive.execution_cost program 8 statement_budget _ _ _ (clean_run xs)
  refine ⟨h.1, h.2.trans ?_⟩
  have ht := input_time_bound xs
  nlinarith

end Counting.Algorithm.KarpLubyRequest.Sampling.TotalMass
