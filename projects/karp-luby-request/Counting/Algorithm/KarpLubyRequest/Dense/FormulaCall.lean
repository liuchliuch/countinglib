import Counting.Algorithm.KarpLubyRequest.Dense.FormulaRaw

/-!
# Halting whole-formula call with the original normalization semantics

The final transition is included so the canonical embedding compiler can return
to a caller. The binary count is the length of the original `normalizeFormula`,
and the materialized rows have that same order and multiplicity by the existing
`DenseNormalization.formula_refines` theorem. The saved variable and raw-formula
words and the complete scratch-stack cleanup remain explicit in the output bank.
-/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Formula
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

/-- The actual halting configuration, including every caller-visible stack. -/
def returned (bit : Bool) (original raw count rows : List Bool) :
    Cfg (Fin 13) Label (Bool × IntegerArithmetic.CarryProtocol.Memory) where
  l := none
  var := (none, cleanMemory bit)
  stk := outputBank original raw count rows

theorem finish_step (bit : Bool) (original raw count rows : List Bool) :
    computer.step (cfg .good (cleanMemory bit) (outputBank original raw count rows)) =
      some (returned bit original raw count rows) := by rfl

/-- Counting physical successful rows counts the original normalized clause
occurrences, including duplicates and the zero-variable empty clause. -/
theorem normalized_count {n : ℕ} (f : DNF.Formula n) :
    (DenseNormalization.formula n f).value.length = (DNF.normalizeFormula f).length := by
  simpa only [List.length_map] using congrArg List.length (DenseNormalization.formula_refines f)

/-- The actual framed row word has polynomial physical length in the two input
dimensions; unused coordinates and duplicate clauses are included in this size. -/
theorem rows_length_le_raw {n : ℕ} (raw : List Bool) (f : DNF.Formula n)
    (hdecode : (Encoding.formula n).decode raw = some f) :
    (CellCodec.rows (DenseNormalization.formula n f).value).length ≤ raw.length * (4 * n + 1) := by
  rw [CellCodec.rows_length _ n (DenseNormalization.formula_lengths f)]
  apply Nat.mul_le_mul_right
  exact (DenseNormalization.formula_count_le f).trans
    (NestedSemantics.list_decode_size (Encoding.list (Encoding.literal n)) hdecode)

/-- A caller can charge both physically present input fields against one raw
request length. No bound on a decoded binary variable count is substituted. -/
theorem rawCost_le_input (n size inputSize : ℕ) (hn : n ≤ inputSize) (hs : size ≤ inputSize) :
    rawCost n size ≤ 23 * inputSize ^ 2 + 76 * inputSize + 11 := by
  have hsq := Nat.mul_le_mul hs hs
  have hprod := Nat.mul_le_mul hn hs
  unfold rawCost
  nlinarith

/-- Complete source execution for `Embedded.run`; one additional real halt is
charged after the already proved raw normalization pipeline. -/
theorem formula_call (old : Bool) (original raw : List Bool) (f : DNF.Formula original.length)
    (hdecode : (Encoding.formula original.length).decode raw = some f) :
    ∃ bit : Bool, ∃ time : ℕ, time ≤ rawCost original.length raw.length + 1 ∧
      RunsExactly computer.step
        (cfg .copy (cleanMemory old) (bank original raw [] [] [] [] [] []))
        (returned bit original raw (encodeNat (DNF.normalizeFormula f).length)
          (CellCodec.rows (DenseNormalization.formula original.length f).value)) time := by
  obtain ⟨bit, time, bound, run⟩ := formula_raw old original raw f hdecode
  rw [normalized_count] at run
  refine ⟨bit, 1 + time, by omega, ?_⟩
  exact run.trans (runsExactly_one (finish_step bit original raw _ _))

/-- The same halted execution is charged by the original primitive interpreter,
including the final halting instruction. -/
theorem formula_call_primitive (old : Bool) (original raw : List Bool)
    (f : DNF.Formula original.length)
    (hdecode : (Encoding.formula original.length).decode raw = some f) :
    ∃ bit : Bool, ∃ time : ℕ, time ≤ rawCost original.length raw.length + 1 ∧
      (Primitive.run program time
        (some (cfg .copy (cleanMemory old) (bank original raw [] [] [] [] [] [])))).2 =
        some (returned bit original raw (encodeNat (DNF.normalizeFormula f).length)
          (CellCodec.rows (DenseNormalization.formula original.length f).value)) ∧
      (Primitive.run program time
        (some (cfg .copy (cleanMemory old) (bank original raw [] [] [] [] [] [])))).1 ≤ 8 * time := by
  obtain ⟨bit, time, bound, run⟩ := formula_call old original raw f hdecode
  exact ⟨bit, time, bound, Primitive.execution_cost program 8 statement_budget _ _ _ run⟩

end Counting.Algorithm.KarpLubyRequest.Dense.Formula
