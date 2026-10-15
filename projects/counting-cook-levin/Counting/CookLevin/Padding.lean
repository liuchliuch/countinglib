import Counting.CookLevin.Evaluator
import PlanarHom.ListReverseMachines
import PlanarHom.RawBooleanListMachine

/-! Exact-length public witnesses use one uniquely determined all-false suffix. -/
namespace Counting.CookLevin
open PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ArithmeticCircuitPrimitives Counting.Foundation

/-- A bounded binary-index prefix machine, using existing reversal/suffix machines. -/
theorem fp_take : FP (BitEncoding.nat.prod boolListEncoding) boolListEncoding
    (fun p => p.2.take p.1) := by
  have hn := fp_fst BitEncoding.nat boolListEncoding
  have hw := fp_snd BitEncoding.nat boolListEncoding
  have hl := hw.comp (ListCodecMachines.fp_length BitEncoding.bool)
  have hd := (hl.pair hn).comp PlanarHom.BinaryArithmetic.fp_subtraction
  have hr := hw.comp (PlanarHom.ListReverseMachines.fp_reverse BitEncoding.bool)
  have hs := (hd.pair hr).comp (PlanarHom.ListDropMachines.fp_drop BitEncoding.bool false)
  exact (hs.comp (PlanarHom.ListReverseMachines.fp_reverse BitEncoding.bool)).congr
    (fun p => by
      change (p.2.reverse.drop (p.2.length - p.1)).reverse = p.2.take p.1
      rw [← List.reverse_take, List.reverse_reverse])

/-- All surplus witness bits must be false, rather than merely being ignored. -/
def accept (p : Instance × List Bool) : Bool :=
  p.1.eval (p.2.take p.1.arity) && !(p.2.drop p.1.arity).any id

theorem noTrue_eq_false_replication (xs : List Bool) :
    (!(xs.any id)) = decide (xs = List.replicate xs.length false) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases a <;> simp [List.replicate_succ, ih]

/-- An encoded instance is long enough to carry its unary witness arity. The
remaining `encodedLength - arity` bits have exactly one accepted filling. -/
theorem accept_count (c : Instance) :
    witnessCount (Instance.encoding.encode c).length (fun w => accept (c,w)) = c.count := by
  let N := (Instance.encoding.encode c).length
  have hN : c.arity + (N - c.arity) = N := Nat.add_sub_of_le (Instance.arity_le_encoded_length c)
  calc
    witnessCount N (fun w => accept (c,w)) =
        witnessCount (c.arity + (N - c.arity)) (fun w => accept (c,w)) := by rw [hN]
    _ = witnessCount (c.arity + (N - c.arity))
        (falsePadding c.arity (N - c.arity) c.eval) := by
      unfold witnessCount
      apply countAccepted_congr
      intro w
      simp only [accept, falsePadding, noTrue_eq_false_replication,
        List.length_drop, List.length_ofFn, Nat.add_sub_cancel_left]
    _ = c.count := witnessCount_falsePadding c.arity (N - c.arity) c.eval

/-- Actual raw witness framing, bounded prefix/suffix scans, evaluation, and
Boolean accumulation provide one deterministic polynomial-time verifier. -/
theorem fp_accept : FP (Instance.encoding.prod BitEncoding.bits) BitEncoding.bool accept := by
  have hc := fp_fst Instance.encoding BitEncoding.bits
  have hw := (fp_snd Instance.encoding BitEncoding.bits).comp PlanarHom.RawBooleanListMachine.fp_boolList
  have hn := (hc.comp (fp_fst BitEncoding.unaryNat (norGateEncoding.list.prod BitEncoding.nat))).comp
    PlanarHom.UnaryNatConversionMachine.fp_conversion
  have hp := (hn.pair hw).comp fp_take
  have he := (hc.pair hp).comp fp_eval
  have hd := (hn.pair hw).comp (PlanarHom.ListDropMachines.fp_drop BitEncoding.bool false)
  have ha := hd.comp (PlanarHom.ListPredicateMachines.fp_any BitEncoding.bool id (fp_id BitEncoding.bool))
  have hz := ha.comp (fp_bool_unary BitEncoding.bool Bool.not)
  exact (he.pair hz).comp (fp_bool_gate (fun p => p.1 && p.2))

end Counting.CookLevin
