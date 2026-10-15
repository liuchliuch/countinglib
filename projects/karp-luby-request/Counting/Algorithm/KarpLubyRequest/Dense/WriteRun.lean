import Counting.Algorithm.KarpLubyRequest.Dense.WriteSteps

/-!
# Checked-write correctness with a physical polynomial execution bound

The mathematical index occurs only in the specification of its encoded stack.
Induction follows the physical dense row. Large out-of-bounds indices therefore
cannot cause execution proportional to their decoded value.
-/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Write
open Turing Computability Holant.Complexity StackProtocol IntegerArithmetic
open Counting.Algorithm.KarpLubyMachine

variable {K Λ τ : Type} [DecidableEq K]

/-- The good exit holds the restored complete row. The bad exit is clean. -/
def finished (st : Stacks K) (lab : Labels Λ) (b : Bool) (memory : τ)
    (frame : K → List Bool) (pref : CellCodec.Cells) (result : Option CellCodec.Cells) :
    Cfg K Λ (Bool × τ) :=
  match result with
  | none => cfg lab.bad (b, memory) (tapes st frame [] [] [] [])
  | some row => cfg lab.good (b, memory) (tapes st frame (CellCodec.encode (pref ++ row)) [] [] [])

variable (step : Cfg K Λ (Bool × τ) → Option (Cfg K Λ (Bool × τ)))
variable (st : Stacks K) (lab : Labels Λ) (exec : Executes step st lab)
variable (b : Bool) (memory : τ) (frame : K → List Bool)
include exec

theorem cell_zero_step (x : Option Bool) (xs : CellCodec.Cells) (pref : List Bool) :
    step (cfg lab.loop (b, memory) (tapes st frame (CellCodec.encode (x :: xs)) [] pref [])) =
      some (cfg lab.write (b, memory) (tapes st frame (CellCodec.encode (x :: xs)) [] pref [])) := by
  cases x <;> simpa only [CellCodec.encode_cons, CellCodec.cell, List.cons_append, List.nil_append] using
    zero_step step st lab exec b memory frame _ _ (CellCodec.encode xs) pref

theorem cell_positive_step (x : Option Bool) (xs : CellCodec.Cells) (counter pref : List Bool)
    (hc : counter ≠ []) :
    step (cfg lab.loop (b, memory) (tapes st frame (CellCodec.encode (x :: xs)) counter pref [])) =
      some (cfg lab.skip (b, memory) (tapes st frame (CellCodec.encode (x :: xs)) counter pref [])) := by
  cases x <;> simpa only [CellCodec.encode_cons, CellCodec.cell, List.cons_append, List.nil_append] using
    positive_step step st lab exec b memory frame _ _ (CellCodec.encode xs) counter pref hc

theorem cell_skip_step (x : Option Bool) (xs pref : CellCodec.Cells) (counter : List Bool) :
    step (cfg lab.skip (b, memory)
      (tapes st frame (CellCodec.encode (x :: xs)) counter (CellCodec.encode pref).reverse [])) =
      some (cfg lab.borrow (b, memory)
        (tapes st frame (CellCodec.encode xs) counter (CellCodec.encode (pref ++ [x])).reverse [])) := by
  cases x <;>
    simpa only [CellCodec.encode_cons, CellCodec.encode_append, CellCodec.encode_nil,
      CellCodec.cell, List.append_nil, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append] using
    skip_step step st lab exec b memory frame _ _ (CellCodec.encode xs) counter (CellCodec.encode pref).reverse

/-- Exact semantic refinement to the existing tail-preserving checked write,
with an actual TM2 transition bound depending only on physical word lengths. -/
theorem write_returns (xs pref : CellCodec.Cells) (j : ℕ) :
    ∃ time : ℕ,
      time ≤ (xs.length + 1) * (2 * (encodeNat j).length + 6) + 2 * pref.length + 3 ∧
      RunsExactly step
        (cfg lab.loop (b, memory)
          (tapes st frame (CellCodec.encode xs) (encodeNat j) (CellCodec.encode pref).reverse []))
        (finished st lab b memory frame pref (DenseNormalization.write j b xs).value) time := by
  induction xs generalizing pref j with
  | nil =>
    have first := runsExactly_one (empty_step step st lab exec b memory frame
      (encodeNat j) (CellCodec.encode pref).reverse)
    have clean := cleanup_exact step st lab exec b memory frame []
      (encodeNat j) (CellCodec.encode pref).reverse
    refine ⟨(encodeNat j).length + 2 * pref.length + 4, ?_, ?_⟩
    · simp only [List.length_nil, Nat.zero_add, Nat.one_mul]
      omega
    · simpa only [CellCodec.encode_nil, List.length_nil, Nat.zero_add, List.length_reverse,
        CellCodec.encode_length, DenseNormalization.write, finished, Nat.add_assoc] using first.trans clean
  | cons x xs ih =>
    cases j with
    | zero =>
      have first := runsExactly_one (cell_zero_step step st lab exec b memory frame x xs
        (CellCodec.encode pref).reverse)
      cases x with
      | none =>
        have second := runsExactly_one (write_none_step step st lab exec b memory frame
          (CellCodec.encode xs) (CellCodec.encode pref).reverse)
        have last := restore_exact step st lab exec b memory frame
          (true :: b :: CellCodec.encode xs) (CellCodec.encode pref).reverse
        refine ⟨2 * pref.length + 3, ?_, ?_⟩
        · omega
        · simpa only [show encodeNat 0 = [] from rfl, DenseNormalization.write, finished,
            CellCodec.encode_append, CellCodec.encode_cons, CellCodec.cell, List.cons_append,
            List.nil_append, List.length_reverse, CellCodec.encode_length, List.reverse_reverse,
            Nat.add_assoc] using (first.trans second).trans last
      | some old =>
        by_cases he : old = b
        · subst old
          have second := runsExactly_one (write_same_step step st lab exec b memory frame
            (CellCodec.encode xs) (CellCodec.encode pref).reverse)
          have last := restore_exact step st lab exec b memory frame
            (true :: b :: CellCodec.encode xs) (CellCodec.encode pref).reverse
          refine ⟨2 * pref.length + 3, ?_, ?_⟩
          · omega
          · simpa only [show encodeNat 0 = [] from rfl, DenseNormalization.write, ↓reduceIte, finished,
              CellCodec.encode_append, CellCodec.encode_cons, CellCodec.cell, List.cons_append,
              List.nil_append, List.length_reverse, CellCodec.encode_length, List.reverse_reverse,
              Nat.add_assoc] using (first.trans second).trans last
        · have second := runsExactly_one (write_conflict_step step st lab exec b memory frame old he
            (CellCodec.encode xs) (CellCodec.encode pref).reverse)
          have last := cleanup_exact step st lab exec b memory frame (CellCodec.encode xs) []
            (CellCodec.encode pref).reverse
          refine ⟨2 * xs.length + 2 * pref.length + 5, ?_, ?_⟩
          · simp only [List.length_cons, show encodeNat 0 = [] from rfl, List.length_nil]
            omega
          · simpa only [show encodeNat 0 = [] from rfl, DenseNormalization.write, he, ↓reduceIte,
              finished, CellCodec.encode_cons, CellCodec.cell, List.cons_append, List.nil_append,
              List.length_reverse, CellCodec.encode_length, List.length_nil, Nat.add_zero,
              Nat.add_assoc] using (first.trans second).trans last
    | succ j =>
      have hc : encodeNat (j + 1) ≠ [] := by
        intro h
        have hz := congrArg decodeNat h
        rw [decode_encodeNat] at hz
        change j + 1 = 0 at hz
        omega
      have first := runsExactly_one (cell_positive_step step st lab exec b memory frame x xs
        (encodeNat (j + 1)) (CellCodec.encode pref).reverse hc)
      have second := runsExactly_one (cell_skip_step step st lab exec b memory frame x xs pref
        (encodeNat (j + 1)))
      have dec := decrement_exact step st lab exec b memory frame (CellCodec.encode xs)
        (encodeNat (j + 1)) (CellCodec.encode (pref ++ [x])).reverse
      rw [decrement_encodeNat, Nat.add_sub_cancel] at dec
      obtain ⟨time, bound, run⟩ := ih (pref ++ [x]) j
      have whole := ((first.trans second).trans dec).trans run
      refine ⟨time + (2 * (borrowCount (encodeNat (j + 1)) + 1) + (1 + 1)), ?_, ?_⟩
      · have hb := borrowCount_le (encodeNat (j + 1))
        have hl := decrement_length_le (encodeNat (j + 1))
        rw [decrement_encodeNat, Nat.add_sub_cancel] at hl
        have hm := Nat.mul_le_mul_left (xs.length + 1) hl
        simp only [List.length_cons, List.length_append, List.length_nil] at bound ⊢
        nlinarith
      · have out : finished st lab b memory frame (pref ++ [x]) (DenseNormalization.write j b xs).value =
            finished st lab b memory frame pref (DenseNormalization.write (j + 1) b (x :: xs)).value := by
          cases h : (DenseNormalization.write j b xs).value <;>
            simp [DenseNormalization.write, h, finished, List.append_assoc]
        rw [out] at whole
        exact whole

end Counting.Algorithm.KarpLubyRequest.Dense.Write
