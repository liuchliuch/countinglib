import Counting.Algorithm.KarpLubyRequest.Whole.CostCore
import Counting.Algorithm.KarpLubyRequest.Preparation.RawBounds

/-!
# Complete polynomial bit cost of the raw request machine

The fixed polynomial includes the actual raw parser, dense normalization,
parameter arithmetic, exact tape gate, both loops, median, rational output,
all physical transfers and cleanup. Invalid inputs also satisfy this bound.
Input length here includes the entire supplied random tape.
-/
namespace Counting.Algorithm.KarpLubyRequest.Whole
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose GraphPreprocessing Polynomial
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

def costPolynomial : Polynomial ℕ := composedPolynomial Preparation.rawPolynomial

/-- The full all-raw polynomial is instantiated with the actual source proof of
preparation, not with a semantic preprocessing oracle or a supplied time bound. -/
theorem run_bounded (raw : List Bool) :
    ∃ time, time ≤ costPolynomial.eval raw.length ∧
      RunsExactly computer.step (initList computer raw)
        (haltList computer (ProgramEncoding.evalBits raw)) time := by
  obtain ⟨time, bound, run⟩ := Preparation.raw_run_bounded raw
  rw [Preparation.halt_eq] at run
  exact run_bounded_of_preparation Preparation.rawPolynomial raw time bound run

def primitiveCostPolynomial : Polynomial ℕ := C machine.primitiveBudget * costPolynomial

/-- Same source, same final configuration, with the original primitive
interpreter's cumulative instruction count bounded by a fixed polynomial. -/
theorem bit_cost (raw : List Bool) :
    ∃ time, time ≤ costPolynomial.eval raw.length ∧
      (Primitive.run machine.program time (some (initList computer raw))).2 =
        some (haltList computer (ProgramEncoding.evalBits raw)) ∧
      (Primitive.run machine.program time (some (initList computer raw))).1 ≤
        primitiveCostPolynomial.eval raw.length := by
  obtain ⟨time, ht, hr⟩ := run_bounded raw
  have measured := primitive_run raw _ time hr
  refine ⟨time, ht, measured.1, ?_⟩
  simp only [primitiveCostPolynomial, eval_mul, eval_C]
  exact measured.2.trans (Nat.mul_le_mul_left _ ht)

/-- A canonical uniform Boolean-stack FP certificate for the deterministic
whole-request evaluator, under the original identity word encoding. -/
def computes : Computes Encoding.bits Encoding.bits ProgramEncoding.evalBits where
  machine := machine
  time := costPolynomial
  outputs raw := by
    let witness := run_bounded raw
    let steps := Classical.choose witness
    have proof := Classical.choose_spec witness
    exact { steps := steps, evals_in_steps := proof.2, steps_le_m := proof.1 }

/-- Random bits are part of this deterministic raw input. PAC and the
parameterized random-tape bound are supplied separately by Accuracy. -/
theorem evalBits_inFP : InFP Encoding.bits Encoding.bits ProgramEncoding.evalBits :=
  computes.inFP

end
end Counting.Algorithm.KarpLubyRequest.Whole

