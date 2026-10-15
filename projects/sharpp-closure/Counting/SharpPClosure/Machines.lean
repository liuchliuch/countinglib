import Counting.SharpPClosure.Basic
import Counting.CookLevin.Padding
import Counting.Bridge.WitnessSharpP
import PlanarHom.UnaryPolynomialMachines

/-!
# Physical prefix, suffix, length, and pair computations

Every FP assertion below is obtained from the existing finite TM2 compilers.
The list fold has a proved accumulator size invariant, pair formation copies
its input, and polynomial evaluation physically emits its unary result.
-/

set_option backward.isDefEq.respectTransparency false

namespace Counting.SharpPClosure

open PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ArithmeticCircuitPrimitives

theorem fold_snoc (z xs : List Bool) :
    xs.foldl (fun acc b => acc ++ [b]) z = z ++ xs := by
  induction xs generalizing z with
  | nil => simp
  | cons b xs ih => simp [ih, List.append_assoc]

/-- The inverse of raw-to-list framing is a real bounded append fold. Each
accumulator is at most the literal input length; no decoder is assumed free. -/
theorem fp_rawWord : FP BitEncoding.bool.list BitEncoding.bits id := by
  have hs : FP BitEncoding.bool BitEncoding.bits (fun b => [b]) :=
    fp_code_view _ _ _ (fun _ => rfl)
  have hb := ((fp_fst BitEncoding.bits BitEncoding.bool).pair
    ((fp_snd BitEncoding.bits BitEncoding.bool).comp hs)).comp fp_append
  have hfold := PlanarHom.ListFoldMachines.fp_foldl BitEncoding.bool BitEncoding.bits
    (fun acc b => acc ++ [b]) hb Polynomial.X (by
      intro z xs i _
      rw [fold_snoc]
      have hx := BitEncoding.list_length_le BitEncoding.bool xs
      have ht := List.length_take_le i xs
      simp only [BitEncoding.bits, id_eq, List.length_append, Polynomial.eval_X,
        BitEncoding.prod_length]
      omega)
  exact (((fp_const BitEncoding.bool.list BitEncoding.bits []).pair
    (fp_id BitEncoding.bool.list)).comp hfold).congr (fun xs => by
      change xs.foldl (fun acc b => acc ++ [b]) [] = xs
      rw [fold_snoc, List.nil_append])

/-- Read the actual raw word length, evaluate the fixed natural-coefficient
polynomial in unary, then convert its fully materialized result to binary. -/
theorem fp_witnessLength (q : Polynomial ℕ) :
    FP BitEncoding.bits BitEncoding.nat (fun x : Bits => q.eval x.length) :=
  ((show FP BitEncoding.bits BitEncoding.unaryNat (fun x : Bits => x.length) from
    ⟨PlanarHom.InputLengthMachine.computer BitEncoding.bits⟩).comp
      (PlanarHom.UnaryPolynomialMachines.fp_eval q)).comp
        PlanarHom.UnaryNatConversionMachine.fp_conversion

/-- A source-independent padding operation for a verifier on a transformed
instance. Its behavior is defined even on short and empty witnesses. -/
def padVerifier (q : Polynomial ℕ) (V : Bits × Bits → Bool) (p : Bits × Bits) : Bool :=
  paddedAccept (q.eval p.1.length) (fun w => V (p.1, w)) p.2

/-- Actual machines calculate the required prefix length, retain the instance,
read the prefix, scan the suffix, and reject insufficient witness length. -/
theorem fp_padVerifier (q : Polynomial ℕ) (V : Bits × Bits → Bool)
    (hV : FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool V) :
    FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool (padVerifier q V) := by
  have hx := fp_fst BitEncoding.bits BitEncoding.bits
  have hw := (fp_snd BitEncoding.bits BitEncoding.bits).comp
    PlanarHom.RawBooleanListMachine.fp_boolList
  have hn := hx.comp (fp_witnessLength q)
  have hp := (hn.pair hw).comp Counting.CookLevin.fp_take
  have hr := hp.comp fp_rawWord
  have he := (hx.pair hr).comp hV
  have hd := (hn.pair hw).comp (PlanarHom.ListDropMachines.fp_drop BitEncoding.bool false)
  have ha := hd.comp (PlanarHom.ListPredicateMachines.fp_any BitEncoding.bool id
    (fp_id BitEncoding.bool))
  have hz := ha.comp (fp_bool_unary BitEncoding.bool Bool.not)
  have hl := hw.comp (ListCodecMachines.fp_length BitEncoding.bool)
  have hshort := (hl.pair hn).comp PlanarHom.BinaryArithmetic.fp_comparison
  have hlong := hshort.comp (fp_bool_unary BitEncoding.bool Bool.not)
  apply (((hlong.pair he).comp (fp_bool_gate (fun p => p.1 && p.2))).pair hz).comp
    (fp_bool_gate (fun p => p.1 && p.2)) |>.congr
  intro p
  have hnot (a b : ℕ) : (!decide (a < b)) = decide (b ≤ a) := by
    by_cases h : a < b
    · simp [h, Nat.not_le_of_lt h]
    · simp [h, Nat.le_of_not_gt h]
  simp only [padVerifier, paddedAccept, Function.comp_apply, id_eq, hnot]

/-- Construct and expose a real framed-pair machine, with the source map and
witness projection running on explicitly saved copies of the same input. -/
noncomputable def liftComputer {R : Bits → Bits}
    (hR : Turing.TM2ComputableInPolyTime BitEncoding.bits.encode BitEncoding.bits.encode R) :
    Turing.TM2ComputableInPolyTime
      (BitEncoding.bits.prod BitEncoding.bits).encode
      (BitEncoding.bits.prod BitEncoding.bits).encode (fun p => (R p.1, p.2)) :=
  PlanarHom.MachinePairing.pairComputers
    (PlanarHom.MachineComposition.composeComputers
      (fstEncodingComputer BitEncoding.bits BitEncoding.bits) hR)
    (sndEncodingComputer BitEncoding.bits BitEncoding.bits)

/-- The literal copying, framing, and cleanup overhead appears in the compiled
run, in addition to both component computations. -/
@[simp] theorem liftComputer_steps {R : Bits → Bits}
    (hR : Turing.TM2ComputableInPolyTime BitEncoding.bits.encode BitEncoding.bits.encode R)
    (p : Bits × Bits) :
    ((liftComputer hR).outputsFun p).steps =
      ((PlanarHom.MachineComposition.composeComputers
        (fstEncodingComputer BitEncoding.bits BitEncoding.bits) hR).outputsFun p).steps +
      ((sndEncodingComputer BitEncoding.bits BitEncoding.bits).outputsFun p).steps +
      2 * ((BitEncoding.bits.prod BitEncoding.bits).encode p).length +
      3 * (R p.1).length + 6 := rfl

/-- Both the reduction instance and the retained witness are the actual
materialized output of the pair-lifting execution. -/
theorem liftComputer_time_bound {R : Bits → Bits}
    (hR : Turing.TM2ComputableInPolyTime BitEncoding.bits.encode BitEncoding.bits.encode R)
    (p : Bits × Bits) :
    ((liftComputer hR).outputsFun p).steps ≤
      (liftComputer hR).time.eval ((BitEncoding.bits.prod BitEncoding.bits).encode p).length :=
  ((liftComputer hR).outputsFun p).steps_le_m

end Counting.SharpPClosure
