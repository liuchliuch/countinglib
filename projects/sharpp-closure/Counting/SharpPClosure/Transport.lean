import Counting.SharpPClosure.Machines
import Counting.Complexity.Reduction

/-!
# Parsimonious downward closure of the public binary #P class

The only inputs are the original reduction and target witness. The source
verifier is compiled here, including preservation of the supplied witness,
instance-length computation, prefix/suffix work, and all representation changes.
-/

set_option backward.isDefEq.respectTransparency false

namespace Counting.SharpPClosure

open Computability Counting.Computation Counting.Complexity
open PlanarHom.Complexity

variable {f g : Bits → ℕ}

/-- The syntax-derived output-size polynomial of the real reduction is fed to
the target witness polynomial. Natural coefficients already ensure monotonicity. -/
noncomputable def sourceWitnessLength
    (r : ParsimoniousReduction (encodingList Bool) (encodingList Bool) f g)
    (w : SharpPWitness (encodingList Bool) g) : Polynomial ℕ :=
  w.witnessLength.comp (PolyTime.outputLengthPolynomial r.machine)

theorem targetWitnessLength_le
    (r : ParsimoniousReduction (encodingList Bool) (encodingList Bool) f g)
    (w : SharpPWitness (encodingList Bool) g) (x : Bits) :
    w.witnessLength.eval (r.map x).length ≤ (sourceWitnessLength r w).eval x.length := by
  rw [sourceWitnessLength, Polynomial.eval_comp]
  exact PlanarHom.MachineComposition.natPolynomial_monotone w.witnessLength
    (r.map_encoded_length_le x)

/-- Literal total predicate used by the constructed source witness. -/
def transportAccept
    (r : ParsimoniousReduction (encodingList Bool) (encodingList Bool) f g)
    (w : SharpPWitness (encodingList Bool) g) (p : Bits × Bits) : Bool :=
  padVerifier w.witnessLength w.accept (r.map p.1, p.2)

/-- Compile prefix/suffix checking around the target's original verifier. The
target verifier is transported to its actual framed input codec by W1. -/
noncomputable def paddedComputer (w : SharpPWitness (encodingList Bool) g) :
    Turing.TM2ComputableInPolyTime
      (BitEncoding.bits.prod BitEncoding.bits).encode BitEncoding.bool.encode
      (padVerifier w.witnessLength w.accept) :=
  Classical.choice (fp_padVerifier w.witnessLength w.accept
    ⟨(Counting.Bridge.WitnessSharpP.toFramedVerifier w.verifier).toTM2ComputableInPolyTime⟩)

/-- Pair lifting preserves the witness while the reduction executes; ordinary
composition starts only once this materialized transformed pair is available. -/
noncomputable def framedComputer
    (r : ParsimoniousReduction (encodingList Bool) (encodingList Bool) f g)
    (w : SharpPWitness (encodingList Bool) g) :
    Turing.TM2ComputableInPolyTime
      (BitEncoding.bits.prod BitEncoding.bits).encode BitEncoding.bool.encode
      (transportAccept r w) :=
  PlanarHom.MachineComposition.composeComputers
    (liftComputer r.machine.toTM2ComputableInPolyTime) (paddedComputer w)

/-- The final public finite-alphabet verifier includes both actual representation
transducers and the finite reachable-alphabet restriction compiler. -/
noncomputable def verifier
    (r : ParsimoniousReduction (encodingList Bool) (encodingList Bool) f g)
    (w : SharpPWitness (encodingList Bool) g) :
    PolyTime (encodingProd (encodingList Bool) (encodingList Bool))
      (Holant.Complexity.taggedBoolEncoding Bool) (transportAccept r w) :=
  Counting.Bridge.WitnessSharpP.toTaggedVerifier (framedComputer r w)

/-- The padding program is charged at the proved encoded output-size bound of
the pair-lifting machine, which includes the preserved witness. -/
@[simp] theorem framedComputer_time
    (r : ParsimoniousReduction (encodingList Bool) (encodingList Bool) f g)
    (w : SharpPWitness (encodingList Bool) g) :
    (framedComputer r w).time =
      (paddedComputer w).time.comp
        (PlanarHom.MachineComposition.outputLengthPolynomial
          (liftComputer r.machine.toTM2ComputableInPolyTime)) +
      (liftComputer r.machine.toTM2ComputableInPolyTime).time := rfl

/-- The exact run contains pair lifting, length and suffix work, and both codec
transductions. The lift's copying/framing overhead is exposed separately. -/
@[simp] theorem verifier_steps
    (r : ParsimoniousReduction (encodingList Bool) (encodingList Bool) f g)
    (w : SharpPWitness (encodingList Bool) g) (p : Bits × Bits) :
    ((verifier r w).outputsFun p).steps =
      (Counting.WitnessMachines.BooleanOutput.toTagged.outputsFun (transportAccept r w p)).steps +
      (((paddedComputer w).outputsFun (r.map p.1, p.2)).steps +
        ((liftComputer r.machine.toTM2ComputableInPolyTime).outputsFun p).steps +
        (Counting.WitnessMachines.TaggedToFramed.polyTime.outputsFun p).steps) := rfl

/-- The constructed finite machine obeys its actual compiled time polynomial on
the whole tagged instance/witness input; no witness operations are free. -/
theorem verifier_time_bound
    (r : ParsimoniousReduction (encodingList Bool) (encodingList Bool) f g)
    (w : SharpPWitness (encodingList Bool) g) (p : Bits × Bits) :
    ((verifier r w).outputsFun p).steps ≤ (verifier r w).time.eval (p.1.length + p.2.length) := by
  simpa only [encodingProd, encodingList, List.length_append, List.length_map, id_eq] using
    ((verifier r w).outputsFun p).steps_le_m

/-- Exact preservation of target counts, independent of any Boolean behavior the
original verifier might have on words of an unintended length. -/
theorem transportAccept_count
    (r : ParsimoniousReduction (encodingList Bool) (encodingList Bool) f g)
    (w : SharpPWitness (encodingList Bool) g) (x : Bits) :
    Foundation.witnessCount ((sourceWitnessLength r w).eval x.length)
      (fun bits => transportAccept r w (x, bits)) = f x := by
  change Foundation.witnessCount ((sourceWitnessLength r w).eval x.length)
    (paddedAccept (w.witnessLength.eval (r.map x).length)
      (fun bits => w.accept (r.map x, bits))) = f x
  rw [witnessCount_paddedAccept _ _ (targetWitnessLength_le r w x)]
  rw [Foundation.witnessCount, Foundation.countAccepted_eq_card]
  exact (w.counts (r.map x)).symm.trans (r.correct x).symm

end Counting.SharpPClosure

namespace Counting.Complexity.ParsimoniousReduction

open Computability Counting.SharpPClosure PlanarHom.Complexity

variable {f g : Bits → ℕ}

/-- Explicit witness transport for genuine parsimonious reductions between raw
binary inputs. All verifier and runtime fields are constructed from the inputs. -/
noncomputable def sharpPWitness
    (r : ParsimoniousReduction (encodingList Bool) (encodingList Bool) f g)
    (w : SharpPWitness (encodingList Bool) g) : SharpPWitness (encodingList Bool) f where
  witnessLength := sourceWitnessLength r w
  accept := transportAccept r w
  verifier := verifier r w
  counts x := (transportAccept_count r w x).symm.trans
    (Foundation.countAccepted_eq_card _)

/-- Public #P is downward closed under the implemented binary parsimonious
reductions, by the explicit witness and finite-machine construction above. -/
theorem inSharpP
    (r : ParsimoniousReduction (encodingList Bool) (encodingList Bool) f g)
    (hg : InSharpP (encodingList Bool) g) : InSharpP (encodingList Bool) f := by
  obtain ⟨w⟩ := hg
  exact ⟨r.sharpPWitness w⟩

end Counting.Complexity.ParsimoniousReduction

namespace Counting.Complexity.ParsimoniousReduces

open Computability PlanarHom.Complexity

theorem inSharpP {f g : Bits → ℕ}
    (r : ParsimoniousReduces (encodingList Bool) (encodingList Bool) f g)
    (hg : InSharpP (encodingList Bool) g) : InSharpP (encodingList Bool) f := by
  obtain ⟨r⟩ := r
  exact r.inSharpP hg

end Counting.Complexity.ParsimoniousReduces

namespace Counting.Complexity.ParsimoniousEquivalent

open Computability PlanarHom.Complexity

theorem inSharpP_iff {f g : Bits → ℕ}
    (r : ParsimoniousEquivalent (encodingList Bool) (encodingList Bool) f g) :
    InSharpP (encodingList Bool) f ↔ InSharpP (encodingList Bool) g :=
  ⟨r.2.inSharpP, r.1.inSharpP⟩

end Counting.Complexity.ParsimoniousEquivalent
