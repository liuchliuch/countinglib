import Counting.Algorithm.KarpLubyRequest.Dense.FormulaRun
import Counting.Algorithm.KarpLubyRequest.NestedSemantics

/-!
# Original raw-formula codec to actual dense rows and a binary count

Both original words are retained. Contradictory terms are dropped, duplicate
clauses stay duplicated, and every successful row retains every ambient
coordinate. All sizes in the bound are physical input-word lengths.
-/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Formula
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

private theorem raw_parts {n : ℕ} (raw : List Bool) (f : DNF.Formula n)
    (h : (Encoding.formula n).decode raw = some f) :
    ∃ header : List Bool, ∃ raws : List (List Bool),
      raw = Encoding.frame header ++ Encoding.frames raws ∧
      raws.mapM (Encoding.list (Encoding.literal n)).decode = some f := by
  change (Encoding.list (Encoding.list (Encoding.literal n))).decode raw = some f at h
  rw [ListFields.list_decode_eq] at h
  cases hs : ListFields.split raw with
  | none => simp [hs] at h
  | some raws =>
    simp only [hs, Option.bind_some] at h
    obtain ⟨header, _, hraw⟩ := (ListFields.split_some_iff raw raws).mp hs
    exact ⟨header, raws, hraw, h⟩

private theorem row_lengths_sum {n : ℕ} (rows : List CellCodec.Cells)
    (h : ∀ row ∈ rows, row.length = n) : (rows.map List.length).sum = n * rows.length := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hr := h row (by simp)
    have ht := ih (fun r hm => h r (by simp [hm]))
    simp [hr, ht, Nat.mul_succ, Nat.add_comm]

/-- A bound for the displayed program, including order restoration and the
existing physical unary-to-binary count machine. -/
def rawCost (n size : ℕ) : ℕ := 2 * size ^ 2 + 21 * n * size + 76 * size + 11

/-- Complete prepared raw-formula call. Output stack 4 holds `encodeNat count`;
stack 12 holds the original framed-row representation. The original variable
word and formula remain on stacks 0 and 8 respectively. -/
theorem formula_raw (old : Bool) (original raw : List Bool) (f : DNF.Formula original.length)
    (hdecode : (Encoding.formula original.length).decode raw = some f) :
    ∃ bit : Bool, ∃ time : ℕ, time ≤ rawCost original.length raw.length ∧
      RunsExactly computer.step
        (cfg .copy (cleanMemory old) (bank original raw [] [] [] [] [] []))
        (cfg .good (cleanMemory bit)
          (outputBank original raw (encodeNat (DenseNormalization.formula original.length f).value.length)
            (CellCodec.rows (DenseNormalization.formula original.length f).value))) time := by
  obtain ⟨header, raws, hraw, hterms⟩ := raw_parts raw f hdecode
  let rows := (DenseNormalization.formula original.length f).value
  have copy := copy_exact old original raw
  have headerRun := header_exact old original raw header (Encoding.frames raws)
  rw [← hraw] at headerRun
  obtain ⟨bit, time, bound, loop⟩ := loop_returns old original raw raws f hterms []
  simp only [CellCodec.rows_nil, List.length_nil, List.replicate_zero, List.append_nil, Nat.add_zero] at loop
  have order := restore_order_exact bit original raw rows.reverse (List.replicate rows.length true)
  simp only [List.reverse_reverse, List.map_reverse, List.sum_reverse, List.length_reverse] at order
  have count := count_call bit original raw (List.replicate rows.length true) (CellCodec.rows rows)
  simp only [List.length_replicate] at count
  have whole := (((copy.trans headerRun).trans loop).trans order).trans count
  refine ⟨bit, (1 + UnaryBinary.ticks [] rows.length) +
    ((4 * (rows.map List.length).sum + 4 * rows.length + 1) +
      (time + ((3 * header.length + 3) + 2 * (raw.length + 1)))), ?_, whole⟩
  have hs : raw.length = 2 * header.length + 1 + 2 * wordBits raws + raws.length := by
    rw [hraw, List.length_append, Encoding.frame_length, Encoding.frames_length]
    simp only [wordBits, Nat.add_assoc]
  have hh : header.length ≤ raw.length := by omega
  have hw : wordBits raws ≤ raw.length := by omega
  have hl : raws.length ≤ raw.length := by omega
  have hf : f.length ≤ raw.length := NestedSemantics.list_decode_size
    (Encoding.list (Encoding.literal original.length)) hdecode
  have hr : rows.length ≤ raw.length := (DenseNormalization.formula_count_le f).trans hf
  have hrow : (rows.map List.length).sum = original.length * rows.length :=
    row_lengths_sum rows (DenseNormalization.formula_lengths f)
  have hc := count_call_bound (List.replicate rows.length true)
  simp only [List.length_replicate] at hc
  have hsq := Nat.mul_le_mul hr hr
  have hp1 := Nat.mul_le_mul_left original.length hw
  have hp2 := Nat.mul_le_mul_left original.length hl
  have hp3 := Nat.mul_le_mul_left original.length hr
  rw [hrow]
  unfold loopCost at bound
  unfold rawCost
  nlinarith

/-- Primitive interpreter cost for exactly the same full execution. -/
theorem formula_raw_primitive (old : Bool) (original raw : List Bool) (f : DNF.Formula original.length)
    (hdecode : (Encoding.formula original.length).decode raw = some f) :
    ∃ bit : Bool, ∃ time : ℕ, time ≤ rawCost original.length raw.length ∧
      (Primitive.run program time (some (cfg .copy (cleanMemory old) (bank original raw [] [] [] [] [] [])))).2 =
        some (cfg .good (cleanMemory bit)
          (outputBank original raw (encodeNat (DenseNormalization.formula original.length f).value.length)
            (CellCodec.rows (DenseNormalization.formula original.length f).value))) ∧
      (Primitive.run program time (some (cfg .copy (cleanMemory old) (bank original raw [] [] [] [] [] [])))).1 ≤ 8 * time := by
  obtain ⟨bit, time, bound, run⟩ := formula_raw old original raw f hdecode
  exact ⟨bit, time, bound, Primitive.execution_cost program 8 statement_budget _ _ _ run⟩

end Counting.Algorithm.KarpLubyRequest.Dense.Formula
