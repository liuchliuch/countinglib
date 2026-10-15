import Counting.CookLevin.Target
import PlanarHom.CountingCookLevinSerializedCorrectness
import Counting.Bridge.PlanarHomSharpP
import Counting.Computation.PolyTime

/-! All target fields are physically compiled from the original bit input. -/
namespace Counting.CookLevin
open PlanarHom.Complexity PlanarHom.SingleTapeNondeterministic
open PlanarHom.CountingCookLevin PlanarHom.Complexity.PairProjectionMachines

/-- The last NOR output is `arity + 4 * gateCount`; all fields are materialized. -/
noncomputable def compile (M : PolynomialMachine) (x : Bits) : Instance :=
  let T := M.time.eval x.length
  let gs := sourceProgram M x
  (T, (gs, T + 4 * gs.length))

theorem fp_compile (M : PolynomialMachine) : FP BitEncoding.bits Instance.encoding (compile M) := by
  have ht := (fp_polynomialClock M.time).comp (fp_snd BitEncoding.bits BitEncoding.unaryNat)
  have hb := ht.comp PlanarHom.UnaryNatConversionMachine.fp_conversion
  have hg := fp_sourceProgram M
  have hl := hg.comp (PlanarHom.Complexity.ListCodecMachines.fp_length gateEncoding)
  have hm := ((fp_const BitEncoding.bits BitEncoding.nat 4).pair hl).comp
    PlanarHom.BinaryArithmetic.fp_multiplication
  have ho := (hb.pair hm).comp PlanarHom.BinaryArithmetic.fp_addition
  exact ht.pair (hg.pair ho)

theorem compile_output_eq (M : PolynomialMachine) (x : Bits) :
    (compile M x).output =
      timeStart M.machine (uniformBlockSize M.machine)
        (finalContext (x, M.time.eval x.length)) + 8 := by
  let T := M.time.eval x.length
  let C := uniformBlockSize M.machine
  let S := stateRegisterCount M.machine (x.length + T)
  change T + 4 * (uniformProgram M.machine (x,T)).length = _
  rw [uniformProgram_length]
  change T + 4 * (T * (1 + C * S) + 3) = T + 4 + 4 * (1 + C * S) * T + 8
  ring

theorem compile_eval (M : PolynomialMachine) (x : Bits)
    (w : Fin (M.time.eval x.length) → Bool) :
    (compile M x).eval (List.ofFn w) =
      serializedValue M.machine x (M.time.eval x.length) w := by
  unfold Instance.eval
  rw [compile_output_eq]
  rfl

/-- The independent target count equals the source machine's accepting count. -/
theorem compile_count (M : PolynomialMachine) (x : Bits) :
    M.count x = (compile M x).count := by
  rw [count_eq_serializedValue]
  unfold Instance.count Counting.Foundation.witnessCount
  change _ = Counting.Foundation.countAccepted
    (fun w : Fin (M.time.eval x.length) → Bool => (compile M x).eval (List.ofFn w))
  simp_rw [compile_eval]
  exact (Counting.Foundation.countAccepted_eq_card _).symm

/-- Finite-support compilation retains the actual source input/output codewords. -/
noncomputable def compiler (M : PolynomialMachine) :
    Counting.Computation.PolyTime BitEncoding.bits.toFinEncoding Instance.encoding.toFinEncoding
      (compile M) :=
  Counting.Bridge.PlanarHomSharpP.finiteComputer (Classical.choice (fp_compile M))

/-- Every emitted metadata bit is charged by the actual finite compiler's
syntax-derived output-length polynomial on the literal source input length. -/
theorem compile_bitlength_le (M : PolynomialMachine) (x : Bits) :
    (Instance.encoding.encode (compile M x)).length ≤
      (Counting.Computation.PolyTime.outputLengthPolynomial (compiler M)).eval x.length :=
  Counting.Computation.PolyTime.encoded_output_length_le (compiler M) x

end Counting.CookLevin
