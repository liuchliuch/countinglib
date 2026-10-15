import Counting.Algorithm.KarpLubyRequest.Whole.Composition
import Counting.Algorithm.KarpLubyRequest.Evaluation.Cost
import Holant.Complexity.BinaryCompose.OutputBound

/-!
# Literal payload size and actual preparation output growth

The payload's four framed fields and unframed random tail are counted exactly.
Its global size bound follows from the preparation program's executed pushes,
including all intermediate storage and final cleanup. No independent space
oracle or bound on the numeric sampling counts is assumed.
-/
namespace Counting.Algorithm.KarpLubyRequest.Whole
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose Polynomial
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

theorem payload_length (rows mass samples groups tape : List Bool) :
    (Preparation.payload rows mass samples groups tape).length =
      1 + 2 * (rows.length + mass.length + samples.length + groups.length) + 4 + tape.length := by
  simp only [Preparation.payload, List.length_cons, List.length_append, Encoding.frame_length]
  omega

theorem evaluation_payload_length (rows mass samples groups tape : List Bool) :
    (Evaluation.payload rows mass samples groups tape).length =
      1 + 2 * (rows.length + mass.length + samples.length + groups.length) + 4 + tape.length := by
  rw [← payload_eq]
  exact payload_length rows mass samples groups tape

/-- All five physical fields are bounded by the actual serialized payload. -/
theorem payload_fields_le (rows mass samples groups tape : List Bool) :
    rows.length ≤ (Preparation.payload rows mass samples groups tape).length ∧
    mass.length ≤ (Preparation.payload rows mass samples groups tape).length ∧
    samples.length ≤ (Preparation.payload rows mass samples groups tape).length ∧
    groups.length ≤ (Preparation.payload rows mass samples groups tape).length ∧
    tape.length ≤ (Preparation.payload rows mass samples groups tape).length := by
  rw [payload_length]
  omega

theorem evaluation_payload_fields_le (rows mass samples groups tape : List Bool) :
    rows.length ≤ (Evaluation.payload rows mass samples groups tape).length ∧
    mass.length ≤ (Evaluation.payload rows mass samples groups tape).length ∧
    samples.length ≤ (Evaluation.payload rows mass samples groups tape).length ∧
    groups.length ≤ (Evaluation.payload rows mass samples groups tape).length ∧
    tape.length ≤ (Evaluation.payload rows mass samples groups tape).length := by
  rw [← payload_eq]
  exact payload_fields_le rows mass samples groups tape

/-- This is a bound on the clean word produced by this exact source execution,
not a separately supplied size annotation for a semantic preprocessor. -/
theorem prepared_output_length (raw payload : List Bool) (prepareTime : ℕ)
    (run : RunsExactly Preparation.computer.step (initList Preparation.computer raw)
      (Preparation.finalConfiguration payload) prepareTime) :
    payload.length ≤ raw.length + prepareTime * Preparation.primitiveBudget := by
  have h := Preparation.stored_bits_from_raw raw (Preparation.finalConfiguration payload)
    prepareTime run
  have hz : stackSize (Preparation.finalConfiguration payload).stk = payload.length := by
    rw [← Preparation.halt_eq]
    exact Preparation.machine.size_halt payload
  rw [hz] at h
  exact h

def outputSizePolynomial (preparePolynomial : Polynomial ℕ) : Polynomial ℕ :=
  X + C Preparation.primitiveBudget * preparePolynomial

theorem outputSizePolynomial_eval (preparePolynomial : Polynomial ℕ) (n : ℕ) :
    (outputSizePolynomial preparePolynomial).eval n =
      n + Preparation.primitiveBudget * preparePolynomial.eval n := by
  simp only [outputSizePolynomial, eval_add, eval_X, eval_mul, eval_C]

/-- An actual preparation time certificate automatically supplies the physical
input bound required by the composed evaluator. -/
theorem prepared_output_length_le_polynomial (raw payload : List Bool) (prepareTime : ℕ)
    (preparePolynomial : Polynomial ℕ)
    (run : RunsExactly Preparation.computer.step (initList Preparation.computer raw)
      (Preparation.finalConfiguration payload) prepareTime)
    (ht : prepareTime ≤ preparePolynomial.eval raw.length) :
    payload.length ≤ (outputSizePolynomial preparePolynomial).eval raw.length := by
  rw [outputSizePolynomial_eval]
  calc
    _ ≤ raw.length + prepareTime * Preparation.primitiveBudget :=
      prepared_output_length raw payload prepareTime run
    _ ≤ raw.length + preparePolynomial.eval raw.length * Preparation.primitiveBudget :=
      Nat.add_le_add_left (Nat.mul_le_mul_right Preparation.primitiveBudget ht) raw.length
    _ = _ := by rw [Nat.mul_comm (preparePolynomial.eval raw.length)]

end
end Counting.Algorithm.KarpLubyRequest.Whole
