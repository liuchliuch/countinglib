import Counting.SharpPClosure
import Counting.Examples.Machines
import Counting.Examples.WitnessVerifier

/-!
# Independent clients that require real padding

The reduction reverses its input on the original two-stack TM2. Its derived
output bound is `2*n+1`, so a length-two instance is assigned five source bits
while its target verifier needs two. The nonconstant verifier accepts exactly
three prefixes, whereas ignoring the three surplus bits would accept 24 words.
-/

set_option backward.isDefEq.respectTransparency false

namespace Counting.SharpPClosure.Clients

open Computability Counting.Computation Counting.Complexity Counting.Foundation
open PlanarHom.Complexity

noncomputable def reverseReduction (h : ℕ → ℕ) :
    ParsimoniousReduction (encodingList Bool) (encodingList Bool)
      (fun x : Bits => h x.length) (fun x : Bits => h x.length) where
  map := List.reverse
  machine := Counting.Examples.reversePolyTime
  correct x := by simp

theorem reverse_outputLength (n : ℕ) :
    (PolyTime.outputLengthPolynomial Counting.Examples.reversePolyTime).eval n = 2*n+1 := by
  have hp : PlanarHom.MachineComposition.machinePushBound
      Counting.Examples.reversePolyTime.tm = 1 := by decide
  simp only [PolyTime.outputLengthPolynomial, PlanarHom.MachineComposition.outputLengthPolynomial,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C,
    Counting.Examples.reversePolyTime, Polynomial.eval_one]
  change n + PlanarHom.MachineComposition.machinePushBound
    Counting.Examples.reversePolyTime.tm * (n + 1) = 2*n+1
  rw [hp]
  omega

noncomputable def nonzeroReduction := reverseReduction (fun n => 2^n-1)
noncomputable def nonzeroTransport := nonzeroReduction.sharpPWitness Counting.Examples.nonzeroWitnesses

theorem nonzero_accept (x bits : Bits) :
    nonzeroTransport.accept (x,bits) = paddedAccept x.length (fun w => w.any id) bits := by
  simp only [nonzeroTransport, nonzeroReduction, ParsimoniousReduction.sharpPWitness,
    transportAccept, padVerifier, reverseReduction, Counting.Examples.nonzeroWitnesses,
    Polynomial.eval_X, List.length_reverse, Counting.Examples.witnessAnyAccept]

theorem nonzero_witnessLength (n : ℕ) : nonzeroTransport.witnessLength.eval n = 2*n+1 := by
  change (Polynomial.X.comp (PolyTime.outputLengthPolynomial
    Counting.Examples.reversePolyTime)).eval n = _
  simpa only [Polynomial.eval_comp, Polynomial.eval_X] using reverse_outputLength n

theorem nonzero_membership :
    InSharpP (encodingList Bool) (fun x : Bits => 2^x.length-1) :=
  nonzeroReduction.inSharpP Counting.Examples.nonzeroWitnesses_inSharpP

/-- Three valid prefixes, each with one false suffix, give exactly three source
witnesses although the source witness is longer than the target witness. -/
theorem nonzero_count_three :
    witnessCount 5 (fun bits => nonzeroTransport.accept ([false,true], bits)) = 3 := by
  have h := transportAccept_count nonzeroReduction Counting.Examples.nonzeroWitnesses [false,true]
  change witnessCount (nonzeroTransport.witnessLength.eval 2)
    (fun bits => nonzeroTransport.accept ([false,true], bits)) = 3 at h
  simpa only [nonzero_witnessLength] using h

theorem accepts_unique_false_padding :
    nonzeroTransport.accept ([false,true], [true,false,false,false,false]) = true := by
  rw [nonzero_accept]
  rfl

theorem rejects_true_padding :
    nonzeroTransport.accept ([false,true], [true,false,false,true,false]) = false := by
  rw [nonzero_accept]
  rfl

theorem rejects_short_witness :
    nonzeroTransport.accept ([false,true], [true]) = false := by
  rw [nonzero_accept]
  rfl

theorem rejects_empty_for_nonempty_prefix :
    nonzeroTransport.accept ([false,true], []) = false := by
  rw [nonzero_accept]
  rfl

/-- The negative control detects the exact factor `2^3`: a verifier that ignores
the suffix would count 24 rather than the correct count 3. -/
theorem ignored_suffix_counts_twenty_four :
    witnessCount 5 (fun bits => (bits.take 2).any id) = 24 := by
  rw [witnessCount_ignored_padding 2 3 (fun bits => bits.any id)]
  have h : witnessCount 2 (fun bits => bits.any id) = 3 := by
    rw [witnessCount, countAccepted_eq_card]
    exact Counting.Examples.witnessAny_card [] 2
  rw [h]
  decide

theorem inflation_is_detected :
    witnessCount 5 (fun bits => (bits.take 2).any id) ≠
      witnessCount 5 (fun bits => nonzeroTransport.accept ([false,true], bits)) := by
  rw [ignored_suffix_counts_twenty_four, nonzero_count_three]
  decide

/-- With an empty target prefix the one source bit must still be false. -/
noncomputable def allTarget : SharpPWitness (encodingList Bool)
    (fun x : Bits => 2^x.length) where
  witnessLength := Polynomial.X
  accept := (allWitnesses (encodingList Bool) Polynomial.X).accept
  verifier := (allWitnesses (encodingList Bool) Polynomial.X).verifier
  counts x := by simp [allWitnesses, encodingList]

noncomputable def allTransport := (reverseReduction (fun n => 2^n)).sharpPWitness allTarget

theorem all_accept (x bits : Bits) :
    allTransport.accept (x,bits) = paddedAccept x.length (fun _ => true) bits := by
  simp only [allTransport, ParsimoniousReduction.sharpPWitness, transportAccept, padVerifier,
    allTarget, allWitnesses, reverseReduction, Polynomial.eval_X, List.length_reverse]

theorem empty_instance_padding_length : allTransport.witnessLength.eval 0 = 1 := by
  change (Polynomial.X.comp (PolyTime.outputLengthPolynomial
    Counting.Examples.reversePolyTime)).eval 0 = 1
  simpa only [Polynomial.eval_comp, Polynomial.eval_X] using reverse_outputLength 0

theorem empty_prefix_false_suffix : allTransport.accept ([], [false]) = true := by
  rw [all_accept]
  rfl
theorem empty_prefix_true_suffix : allTransport.accept ([], [true]) = false := by
  rw [all_accept]
  rfl
theorem empty_witness_behavior : allTransport.accept ([], []) = true := by
  rw [all_accept]
  rfl

/-- Accepting the empty word is total-predicate behavior; it is outside the
one-bit source witness space for this instance and is therefore not overcounted. -/
theorem empty_prefix_count_one :
    witnessCount 1 (fun bits => allTransport.accept ([],bits)) = 1 := by
  have h := transportAccept_count (reverseReduction (fun n => 2^n)) allTarget []
  change witnessCount (allTransport.witnessLength.eval 0)
    (fun bits => allTransport.accept ([],bits)) = 1 at h
  simpa only [empty_instance_padding_length] using h

/-- A genuinely zero-bit witness also survives transport under a constant
witness-length polynomial, and still has the unique empty choice. -/
noncomputable def zeroBitTarget : SharpPWitness (encodingList Bool) (fun _ : Bits => 1) where
  witnessLength := 0
  accept := (allWitnesses (encodingList Bool) 0).accept
  verifier := (allWitnesses (encodingList Bool) 0).verifier
  counts x := by simp [allWitnesses]

noncomputable def zeroBitTransport :=
  (reverseReduction (fun _ => 1)).sharpPWitness zeroBitTarget

theorem zeroBit_length : zeroBitTransport.witnessLength = 0 := by
  change (0 : Polynomial ℕ).comp _ = 0
  simp

theorem zeroBit_count_one (x : Bits) :
    witnessCount 0 (fun bits => zeroBitTransport.accept (x,bits)) = 1 := by
  have h := transportAccept_count (reverseReduction (fun _ => 1)) zeroBitTarget x
  change witnessCount (zeroBitTransport.witnessLength.eval x.length)
    (fun bits => zeroBitTransport.accept (x,bits)) = 1 at h
  simpa only [zeroBit_length, Polynomial.eval_zero] using h

/-- An end-to-end machine client: its certified execution on the padded witness
terminates within the polynomial at the literal seven-symbol tagged input. -/
theorem padded_machine_runtime :
    (nonzeroTransport.verifier.outputsFun
      ([false,true], [true,false,false,false,false])).steps ≤
      nonzeroTransport.verifier.time.eval 7 :=
  verifier_time_bound nonzeroReduction Counting.Examples.nonzeroWitnesses _

/-- Physical pair lifting on a non-palindrome retains every witness bit. The
copy/framing/cleanup overhead alone is exactly 32 transitions for this input. -/
theorem retained_pair_steps :
    ((liftComputer Counting.Examples.reversePolyTime.toTM2ComputableInPolyTime).outputsFun
      ([false,true], [true,false,false,false,false])).steps =
      (Counting.Examples.reversePolyTime.outputsFun [false,true]).steps +
      ((PairProjectionMachines.fstEncodingComputer BitEncoding.bits BitEncoding.bits).outputsFun
        ([false,true], [true,false,false,false,false])).steps +
      ((PairProjectionMachines.sndEncodingComputer BitEncoding.bits BitEncoding.bits).outputsFun
        ([false,true], [true,false,false,false,false])).steps + 32 := by
  rw [liftComputer_steps, PlanarHom.MachineComposition.composeComputers_steps]
  simp only [BitEncoding.prod_length, BitEncoding.bits, id_eq, List.length_cons,
    List.length_nil, List.length_reverse]

/-- The complete pair-lifting run physically changes the instance order and
preserves the entire witness, including its nonempty false suffix. -/
noncomputable def retained_pair_output :
    let m := liftComputer Counting.Examples.reversePolyTime.toTM2ComputableInPolyTime
    Turing.TM2OutputsInTime m.tm
      (((BitEncoding.bits.prod BitEncoding.bits).encode
        ([false,true], [true,false,false,false,false])).map m.inputAlphabet.symm)
      (some (((BitEncoding.bits.prod BitEncoding.bits).encode
        ([true,false], [true,false,false,false,false])).map m.outputAlphabet.symm))
      (m.time.eval 10) := by
  exact (liftComputer Counting.Examples.reversePolyTime.toTM2ComputableInPolyTime).outputsFun
    ([false,true], [true,false,false,false,false])

/-- The composed verifier reaches a clean halting configuration containing the
encoded Boolean true for the padded accepting witness. -/
noncomputable def padded_machine_output :
    let m := nonzeroTransport.verifier
    Turing.TM2OutputsInTime m.tm
      (((encodingProd (encodingList Bool) (encodingList Bool)).encode
        ([false,true], [true,false,false,false,false])).map m.inputAlphabet.symm)
      (some ([Sum.inr true].map m.outputAlphabet.symm)) (m.time.eval 7) := by
  have h := nonzeroTransport.verifier.outputsFun
    ([false,true], [true,false,false,false,false])
  rw [accepts_unique_false_padding] at h
  exact h

def boundaryChecks : Bool :=
  paddedAccept 2 (fun bits => bits.any id) [true,false,false,false,false] &&
  !paddedAccept 2 (fun bits => bits.any id) [true,false,false,true,false] &&
  !paddedAccept 2 (fun bits => bits.any id) [true] &&
  !paddedAccept 2 (fun bits => bits.any id) [] &&
  paddedAccept 0 (fun _ => true) [false] &&
  !paddedAccept 0 (fun _ => true) [true] &&
  paddedAccept 0 (fun _ => true) []

theorem boundaryChecks_pass : boundaryChecks = true := rfl

end Counting.SharpPClosure.Clients
