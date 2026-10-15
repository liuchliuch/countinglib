import Counting.WitnessMachines.FramedToTagged
import Counting.WitnessMachines.BooleanOutput
import Counting.Bridge.PlanarHomSharpP

/-!
# A concrete representation bridge for the public bit-string #P interface

Both directions compile three real finite machines: input pair transducer,
verifier, and Boolean output transducer. Polynomial time comes from F1's actual
composition compiler and source-derived intermediate output-length bound.
The accepted witness predicate and exact witness length remain identical.
-/
namespace Counting.Bridge.WitnessSharpP
open Computability Counting.Computation PlanarHom.Complexity
open Counting.WitnessMachines

/-- Compile an ordinary PH verifier to the public tagged finite-machine format. -/
noncomputable def toTaggedVerifier {V : Bits × Bits → Bool}
    (h : Turing.TM2ComputableInPolyTime
      (BitEncoding.bits.prod BitEncoding.bits).encode BitEncoding.bool.encode V) :
    PolyTime TaggedToFramed.taggedPair (Holant.Complexity.taggedBoolEncoding Bool) V := by
  let first := PolyTime.comp TaggedToFramed.polyTime (PlanarHomSharpP.finiteComputer h)
  let result := PolyTime.comp first BooleanOutput.toTagged
  exact result

/-- Compile a public verifier back to the original actual framed pair format. -/
noncomputable def toFramedVerifier {V : Bits × Bits → Bool}
    (h : PolyTime TaggedToFramed.taggedPair (Holant.Complexity.taggedBoolEncoding Bool) V) :
    PolyTime TaggedToFramed.framedPair BitEncoding.bool.toFinEncoding V := by
  let first := PolyTime.comp FramedToTagged.polyTime h
  let result := PolyTime.comp first BooleanOutput.fromTagged
  exact result

/-- Composition preserves the exact three constituent transition counts. -/
@[simp] theorem toTaggedVerifier_steps {V : Bits × Bits → Bool}
    (h : Turing.TM2ComputableInPolyTime
      (BitEncoding.bits.prod BitEncoding.bits).encode BitEncoding.bool.encode V) (pair : Bits × Bits) :
    ((toTaggedVerifier h).outputsFun pair).steps =
      (BooleanOutput.toTagged.outputsFun (V pair)).steps +
        ((h.outputsFun pair).steps + (TaggedToFramed.polyTime.outputsFun pair).steps) := rfl

@[simp] theorem toFramedVerifier_steps {V : Bits × Bits → Bool}
    (h : PolyTime TaggedToFramed.taggedPair (Holant.Complexity.taggedBoolEncoding Bool) V)
    (pair : Bits × Bits) :
    ((toFramedVerifier h).outputsFun pair).steps =
      (BooleanOutput.fromTagged.outputsFun (V pair)).steps +
        ((h.outputsFun pair).steps + (FramedToTagged.polyTime.outputsFun pair).steps) := rfl

/-- A concrete independent accepting-path machine produces a concrete public
witness, using its actual replay program and the representation compilers. -/
noncomputable def acceptingMachineWitness (M : PolynomialNondeterministicMachine) :
    Counting.Complexity.SharpPWitness (encodingList Bool) M.count where
  witnessLength := M.time
  accept := PlanarHom.NondeterministicReplayCompiler.verifier M.machine
  verifier := toTaggedVerifier (PlanarHom.NondeterministicReplayCompiler.computer M.machine)
  counts := M.count_eq_certificateCount

/-- The reverse translation physically prepares the witness length, branches
once per witness bit, and runs the compiled framed verifier. -/
noncomputable def witnessAcceptingMachine {f : Bits → ℕ}
    (w : Counting.Complexity.SharpPWitness (encodingList Bool) f) :
    PolynomialNondeterministicMachine :=
  PlanarHom.CertificateNondeterministicCompiler.compile w.witnessLength w.accept
    ⟨(toFramedVerifier w.verifier).toTM2ComputableInPolyTime⟩

/-- Each accepted witness contributes exactly one path of the constructed machine. -/
theorem witnessAcceptingMachine_count {f : Bits → ℕ}
    (w : Counting.Complexity.SharpPWitness (encodingList Bool) f) (x : Bits) :
    (witnessAcceptingMachine w).count x = f x := by
  exact (PlanarHom.CertificateNondeterministicCompiler.count_eq_certificateCount
    w.witnessLength w.accept _ x).trans (w.counts x).symm

/-- The exact witness predicate and length polynomial need no padding change. -/
theorem certificateSharpP_inSharpP {f : Bits → ℕ} (h : CertificateSharpP f) :
    Counting.Complexity.InSharpP (encodingList Bool) f := by
  obtain ⟨p, V, ⟨computer⟩, counts⟩ := h
  exact ⟨{
    witnessLength := p
    accept := V
    verifier := toTaggedVerifier computer
    counts := counts }⟩

/-- Public finite-machine witnesses compile to the original certificate class. -/
theorem inSharpP_certificateSharpP {f : Bits → ℕ}
    (h : Counting.Complexity.InSharpP (encodingList Bool) f) : CertificateSharpP f := by
  obtain ⟨w⟩ := h
  exact ⟨w.witnessLength, w.accept,
    ⟨(toFramedVerifier w.verifier).toTM2ComputableInPolyTime⟩, w.counts⟩

theorem bits_inSharpP_iff_certificateSharpP (f : Bits → ℕ) :
    Counting.Complexity.InSharpP (encodingList Bool) f ↔ CertificateSharpP f :=
  ⟨inSharpP_certificateSharpP, certificateSharpP_inSharpP⟩

/-- The public witness interface agrees with independent finite-alphabet
accepting paths, by both actual pair/output transducers and the PH compilers. -/
theorem bits_inSharpP_iff_acceptingPaths (f : Bits → ℕ) :
    Counting.Complexity.InSharpP (encodingList Bool) f ↔ SharpP f :=
  (bits_inSharpP_iff_certificateSharpP f).trans (sharpP_iff_certificateSharpP f).symm

end Counting.Bridge.WitnessSharpP
