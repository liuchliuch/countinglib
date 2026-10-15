import Counting.CookLevin.Padding
import Counting.Bridge.WitnessSharpP

/-! Concrete finite machines place the independently encoded NOR target in #P. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Counting.CookLevin
open Computability Counting.Computation PlanarHom.Complexity
open Counting.WitnessMachines

/-- Reuse the actual W1 transducer on arbitrary instance codewords. It copies the
literal encoded instance; no arbitrary decode or representation invariance is assumed. -/
def taggedToFramed {A : Type} (ea : BitEncoding A) :
    PolyTime (encodingProd ea.toFinEncoding (encodingList Bool))
      (ea.prod BitEncoding.bits).toFinEncoding id where
  tm := TaggedToFramed.machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 4
  outputsFun pair := by
    have h := TaggedToFramed.outputs (ea.encode pair.1) pair.2
    refine { steps := h.steps, evals_in_steps := ?_, steps_le_m := ?_ }
    · simp only [Equiv.refl, List.map_id]
      exact h.evals_in_steps
    · apply h.steps_le_m.trans
      simp only [encodingProd, encodingList, BitEncoding.toFinEncoding,
        List.length_append, List.length_map, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, id_eq]
      omega
  finiteAlphabets := TaggedToFramed.alphabetFintype

/-- Compile framed source verifier code into the public tagged pair interface. -/
def verifier : PolyTime
    (encodingProd Instance.encoding.toFinEncoding (encodingList Bool))
    (Holant.Complexity.taggedBoolEncoding Bool) accept :=
  PolyTime.comp
    (PolyTime.comp (taggedToFramed Instance.encoding)
      (Counting.Bridge.PlanarHomSharpP.finiteComputer (Classical.choice fp_accept)))
    BooleanOutput.toTagged

/-- The full input bit length dominates the physically unary witness arity.
Exactly that many guessed bits are used, with a unique false suffix. -/
def sharpPWitness : Counting.Complexity.SharpPWitness Instance.encoding.toFinEncoding Instance.count where
  witnessLength := Polynomial.X
  accept := accept
  verifier := verifier
  counts c := by
    calc
      c.count = Counting.Foundation.witnessCount
          ((Polynomial.X : Polynomial ℕ).eval (Instance.encoding.toFinEncoding.encode c).length)
          (fun w => accept (c,w)) := by
        simpa only [Polynomial.eval_X, BitEncoding.toFinEncoding] using (accept_count c).symm
      _ = _ := Counting.Foundation.countAccepted_eq_card _

theorem target_inSharpP : Counting.Complexity.InSharpP Instance.encoding.toFinEncoding Instance.count :=
  ⟨sharpPWitness⟩

end Counting.CookLevin
