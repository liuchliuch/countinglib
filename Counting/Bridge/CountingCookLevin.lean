import Counting.Bridge.WitnessSharpP
import Counting.CookLevin
import PlanarHom.SingleTapeSharpPBridge
import PlanarHom.CountingCookLevinSerializedCorrectness

/-!
# The public bit-string #P interface has an actual counting NOR compiler

The compiler emits a materialized list of binary gate-reference pairs. Its source
clock is physically computed in unary by the existing polynomial-time machine.
Only the original time-indexed witness bits are free; auxiliary gate values are
computed, never guessed. The finite-support compiler retains source codewords,
time polynomial and exact step counts. No CNF parser or graph-reduction endpoint
is asserted by this interface. The imported `Counting.CookLevin` package now
additionally supplies the independent typed NOR target, its public #P membership,
and an actual parsimonious reduction from every standard-bit public #P function.
-/

noncomputable section

namespace Counting.Bridge.CountingCookLevin

open PlanarHom.Complexity PlanarHom.SingleTapeNondeterministic
open PlanarHom.CountingCookLevin

/-- Both actual model compilers preserve the source count on standard bit input. -/
theorem bits_inSharpP_iff_singleTapeSharpP (f : Bits → ℕ) :
    Counting.Complexity.InSharpP (Computability.encodingList Bool) f ↔ SingleTapeSharpP f :=
  (WitnessSharpP.bits_inSharpP_iff_acceptingPaths f).trans (sharpP_iff_singleTapeSharpP f)

/-- Select the existing timed machine for the actual serialized source program. -/
def sourceComputer (M : PolynomialMachine) :
    Turing.TM2ComputableInPolyTime BitEncoding.bits.encode gateEncoding.list.encode
      (sourceProgram M) :=
  Classical.choice (fp_sourceProgram M)

/-- An actual all-stack-finite F1 compiler with the original external codecs. -/
def compiler (M : PolynomialMachine) :
    Counting.Computation.PolyTime BitEncoding.bits.toFinEncoding gateEncoding.list.toFinEncoding
      (sourceProgram M) :=
  PlanarHomSharpP.finiteComputer (sourceComputer M)

@[simp] theorem compiler_time (M : PolynomialMachine) :
    (compiler M).time = (sourceComputer M).time := rfl

@[simp] theorem compiler_steps (M : PolynomialMachine) (x : Bits) :
    ((compiler M).outputsFun x).steps = ((sourceComputer M).outputsFun x).steps := rfl

/-- The returned gate list has the exact source-derived size, including final gates. -/
theorem sourceProgram_length (M : PolynomialMachine) (x : Bits) :
    (sourceProgram M x).length = M.time.eval x.length *
      (1 + uniformBlockSize M.machine *
        stateRegisterCount M.machine (x.length + M.time.eval x.length)) + 3 :=
  uniformProgram_length M.machine (x, M.time.eval x.length)

/-- Actual serialization preserves the public finite count, with no free gate bits. -/
theorem source_count_eq_countAccepted (M : PolynomialMachine) (x : Bits) :
    M.count x = Counting.Foundation.countAccepted
      (serializedValue M.machine x (M.time.eval x.length)) := by
  rw [Counting.Foundation.countAccepted_eq_card]
  exact count_eq_serializedValue M x

/-- Every public standard-bit #P function has a finite polynomial-time compiler
whose actual output NOR program preserves its accepted witness count. The input
and output encodings are the explicitly retained source encodings. -/
theorem bits_inSharpP_compiles_to_counting_nor {f : Bits → ℕ}
    (hf : Counting.Complexity.InSharpP (Computability.encodingList Bool) f) :
    ∃ M : PolynomialMachine,
      Counting.Computation.InFP BitEncoding.bits.toFinEncoding gateEncoding.list.toFinEncoding
        (sourceProgram M) ∧
      ∀ x, f x = Counting.Foundation.countAccepted
        (serializedValue M.machine x (M.time.eval x.length)) := by
  obtain ⟨M, hM⟩ := (bits_inSharpP_iff_singleTapeSharpP f).mp hf
  exact ⟨M, ⟨compiler M⟩, fun x => (hM x).trans (source_count_eq_countAccepted M x)⟩

end Counting.Bridge.CountingCookLevin
