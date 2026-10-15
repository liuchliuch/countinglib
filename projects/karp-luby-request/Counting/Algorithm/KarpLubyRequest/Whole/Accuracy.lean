import Counting.Algorithm.KarpLubyRequest.Whole.Cost
import Counting.Algorithm.KarpLubyRequest.RequestSize
import Counting.Algorithm.KarpLuby.Guarantee

/-!
# Relative accuracy of the actual complete finite program

The probability space is the original uniform finite Boolean tape. Every tape
is encoded by the original request codec and executed by the same fixed whole
machine. Successful outcomes are literal clean halts with rational output bytes,
not merely values of a separately analyzed semantic function.
The actual all-raw cost polynomial is composed with the original random-bit
budget polynomial. Its argument is deterministic request-prefix length plus
the strict integer inverse-accuracy adapter, with no hidden tape-size argument.
The randomized model remains this uniform finite tape and fixed deterministic
Boolean-stack program; no different probabilistic transition system is assumed.
-/
namespace Counting.Algorithm.KarpLubyRequest.Whole.Accuracy
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby
open HiddenCircuits.Approximation.SelfReduction

variable {n : ℕ}

/-- Every tape executes to the exact rational analyzed by the original PAC
theorem. The endpoint clears all non-output stacks and resets finite memory. -/
theorem run_on_tape (f : DNF.Formula n) (epsilon delta : ℚ)
    (hvalid : Program.ValidRequest epsilon delta)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    ∃ time, RunsExactly computer.step
      (initList computer (ProgramEncoding.encodeRun f epsilon delta tape))
      (haltList computer (Encoding.encodeOutput (Program.run f epsilon delta tape))) time := by
  obtain ⟨time, hr⟩ := Whole.run (ProgramEncoding.encodeRun f epsilon delta tape)
  rw [ProgramEncoding.evalBits_encodeRun f epsilon delta hvalid tape] at hr
  exact ⟨time, hr⟩

/-- At least 1−δ of the original fair tapes yield an actual clean halt within
the requested relative-error interval. This statement has no time premise. -/
theorem success (f : DNF.Formula n) (epsilon delta : ℚ)
    (hvalid : Program.ValidRequest epsilon delta) :
    1 - delta ≤ probability (fun tape : CoinTape (Program.requestedBudget f epsilon delta) =>
      ∃ time : ℕ, ∃ z : ℚ,
        RunsExactly computer.step
          (initList computer (ProgramEncoding.encodeRun f epsilon delta tape))
          (haltList computer (Encoding.encodeOutput z)) time ∧
        |z - DNF.modelCount f| ≤ epsilon * DNF.modelCount f) := by
  apply (Program.run_success f epsilon delta hvalid.1 hvalid.2.2.1).trans
  apply probability_mono
  intro tape hgood
  obtain ⟨time, hr⟩ := run_on_tape f epsilon delta hvalid tape
  exact ⟨time, Program.run f epsilon delta tape, hr, hgood⟩

/-- Zero target counts are exact on every tape of the original budget. -/
theorem zero (f : DNF.Formula n) (epsilon delta : ℚ)
    (hvalid : Program.ValidRequest epsilon delta) (hz : DNF.modelCount f = 0)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    ∃ time, RunsExactly computer.step
      (initList computer (ProgramEncoding.encodeRun f epsilon delta tape))
      (haltList computer (Encoding.encodeOutput 0)) time := by
  obtain ⟨time, hr⟩ := run_on_tape f epsilon delta hvalid tape
  rw [Program.run_zero f epsilon delta hz tape] at hr
  exact ⟨time, hr⟩

/-- Every tape has a bounded actual execution, with the complete input length
including precisely the finite random tape being sampled. -/
theorem bounded_on_tape (f : DNF.Formula n) (epsilon delta : ℚ)
    (hvalid : Program.ValidRequest epsilon delta)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    ∃ time, time ≤ Whole.costPolynomial.eval (RequestSize.wholeLength f epsilon delta) ∧
      RunsExactly computer.step
        (initList computer (ProgramEncoding.encodeRun f epsilon delta tape))
        (haltList computer (Encoding.encodeOutput (Program.run f epsilon delta tape))) time := by
  obtain ⟨time, ht, hr⟩ := Whole.run_bounded (ProgramEncoding.encodeRun f epsilon delta tape)
  rw [RequestSize.encodeRun_length] at ht
  rw [ProgramEncoding.evalBits_encodeRun f epsilon delta hvalid tape] at hr
  exact ⟨time, ht, hr⟩

/-- PAC for actual executions bounded by the same fixed physical-input
polynomial. The bound applies to every tape, including unsuccessful estimates. -/
theorem bounded_success (f : DNF.Formula n) (epsilon delta : ℚ)
    (hvalid : Program.ValidRequest epsilon delta) :
    1 - delta ≤ probability (fun tape : CoinTape (Program.requestedBudget f epsilon delta) =>
      ∃ time : ℕ, ∃ z : ℚ,
        time ≤ Whole.costPolynomial.eval (RequestSize.wholeLength f epsilon delta) ∧
        RunsExactly computer.step
          (initList computer (ProgramEncoding.encodeRun f epsilon delta tape))
          (haltList computer (Encoding.encodeOutput z)) time ∧
        |z - DNF.modelCount f| ≤ epsilon * DNF.modelCount f) := by
  apply (Program.run_success f epsilon delta hvalid.1 hvalid.2.2.1).trans
  apply probability_mono
  intro tape hgood
  obtain ⟨time, ht, hr⟩ := bounded_on_tape f epsilon delta hvalid tape
  exact ⟨time, Program.run f epsilon delta tape, ht, hr, hgood⟩

/-- The deterministic prefix counts the formula and both rational encodings.
Confidence is therefore charged by its exact input representation. -/
def parameterSize (f : DNF.Formula n) (epsilon delta : ℚ) : ℕ :=
  RequestSize.requestLength f epsilon delta + reciprocalCeiling epsilon

noncomputable def parameterPolynomial : Polynomial ℕ :=
  Whole.costPolynomial.comp RequestSize.boundPolynomial

noncomputable def parameterPrimitivePolynomial : Polynomial ℕ :=
  Polynomial.C machine.primitiveBudget * parameterPolynomial

theorem parameter_time_le (f : DNF.Formula n) (epsilon delta : ℚ) :
    Whole.costPolynomial.eval (RequestSize.wholeLength f epsilon delta) ≤
      parameterPolynomial.eval (parameterSize f epsilon delta) := by
  rw [parameterPolynomial, Polynomial.eval_comp]
  exact natPolynomial_eval_mono _ (RequestSize.wholeLength_le_polynomial f epsilon delta)

/-- All requested fair bits themselves have a polynomial bound in the same
parameters; the time statement does not hide an arbitrarily long random tape. -/
theorem random_bits_le (f : DNF.Formula n) (epsilon delta : ℚ) :
    Program.requestedBudget f epsilon delta ≤
      RequestSize.boundPolynomial.eval (parameterSize f epsilon delta) := by
  apply le_trans (show Program.requestedBudget f epsilon delta ≤
    RequestSize.wholeLength f epsilon delta from Nat.le_add_left _ _)
  exact RequestSize.wholeLength_le_polynomial f epsilon delta

/-- For positive accuracy, the additional numeric argument is bounded by
1/epsilon + 1, retaining the original strict ceiling convention. -/
theorem parameterSize_le_inverse (f : DNF.Formula n) {epsilon : ℚ}
    (he : 0 < epsilon) (delta : ℚ) :
    (parameterSize f epsilon delta : ℚ) ≤
      (RequestSize.requestLength f epsilon delta : ℚ) + (1 / epsilon + 1) := by
  unfold parameterSize
  rw [Nat.cast_add]
  exact add_le_add le_rfl (reciprocalCeiling_le_inv_add_one he)

/-- A uniform actual execution bound with no random-tape length on its right
hand side. The final rational bytes are still those of the original estimator. -/
theorem parameterized_on_tape (f : DNF.Formula n) (epsilon delta : ℚ)
    (hvalid : Program.ValidRequest epsilon delta)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    ∃ time, time ≤ parameterPolynomial.eval (parameterSize f epsilon delta) ∧
      RunsExactly computer.step
        (initList computer (ProgramEncoding.encodeRun f epsilon delta tape))
        (haltList computer (Encoding.encodeOutput (Program.run f epsilon delta tape))) time := by
  obtain ⟨time, ht, hr⟩ := bounded_on_tape f epsilon delta hvalid tape
  exact ⟨time, ht.trans (parameter_time_le f epsilon delta), hr⟩

/-- The same execution has a polynomial bound on actual Primitive instruction
cost, including parsing, all transfers and final cleanup. -/
theorem parameterized_bit_cost (f : DNF.Formula n) (epsilon delta : ℚ)
    (hvalid : Program.ValidRequest epsilon delta)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    ∃ time, time ≤ parameterPolynomial.eval (parameterSize f epsilon delta) ∧
      (Holant.Complexity.GraphPreprocessing.Primitive.run machine.program time
        (some (initList computer (ProgramEncoding.encodeRun f epsilon delta tape)))).2 =
        some (haltList computer (Encoding.encodeOutput (Program.run f epsilon delta tape))) ∧
      (Holant.Complexity.GraphPreprocessing.Primitive.run machine.program time
        (some (initList computer (ProgramEncoding.encodeRun f epsilon delta tape)))).1 ≤
        parameterPrimitivePolynomial.eval (parameterSize f epsilon delta) := by
  obtain ⟨time, ht, hr⟩ := parameterized_on_tape f epsilon delta hvalid tape
  have hm := Whole.primitive_run _ _ time hr
  refine ⟨time, ht, hm.1, ?_⟩
  simp only [parameterPrimitivePolynomial, Polynomial.eval_mul, Polynomial.eval_C]
  exact hm.2.trans (Nat.mul_le_mul_left _ ht)

/-- Relative accuracy and actual finite-program time in the same event. Together
with `random_bits_le` and `parameterized_bit_cost`, this is the finite-fair-tape
FPRAS contract for the original canonical request representation. -/
theorem parameterized_success (f : DNF.Formula n) (epsilon delta : ℚ)
    (hvalid : Program.ValidRequest epsilon delta) :
    1 - delta ≤ probability (fun tape : CoinTape (Program.requestedBudget f epsilon delta) =>
      ∃ time : ℕ, ∃ z : ℚ,
        time ≤ parameterPolynomial.eval (parameterSize f epsilon delta) ∧
        RunsExactly computer.step
          (initList computer (ProgramEncoding.encodeRun f epsilon delta tape))
          (haltList computer (Encoding.encodeOutput z)) time ∧
        |z - DNF.modelCount f| ≤ epsilon * DNF.modelCount f) := by
  apply (Program.run_success f epsilon delta hvalid.1 hvalid.2.2.1).trans
  apply probability_mono
  intro tape hgood
  obtain ⟨time, ht, hr⟩ := parameterized_on_tape f epsilon delta hvalid tape
  exact ⟨time, Program.run f epsilon delta tape, ht, hr, hgood⟩

end Counting.Algorithm.KarpLubyRequest.Whole.Accuracy
