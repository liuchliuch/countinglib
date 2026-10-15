import PlanarHom.SharpPBridge
import Counting.Complexity.SharpP
import Counting.Foundation.Witness

/-!
# Actual accepting-path compilers and the common finite-machine interface

The machine conversion below invokes the source's finite reachable-alphabet
restriction compiler. It preserves codewords, time and exact transition counts.
The source certificate pair codec is framed binary; F1's witness pair codec is
tagged. No equivalence between those different witness interfaces is asserted
without an actual codec-translating machine.
-/
namespace Counting.Bridge.PlanarHomSharpP

open PlanarHom.Complexity Turing

/-- The independently defined finite-alphabet accepting-path class. -/
abbrev AcceptingPaths := PlanarHom.Complexity.SharpP
abbrev Certificates := PlanarHom.Complexity.CertificateSharpP

theorem acceptingPaths_iff_certificates (f : Bits → ℕ) :
    AcceptingPaths f ↔ Certificates f := PlanarHom.Complexity.sharpP_iff_certificateSharpP f

/-- A real restriction compiler supplies every internal alphabet certificate. -/
noncomputable def finiteComputer {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β}
    {f : α → β} (h : TM2ComputableInPolyTime ea.encode eb.encode f) :
    Holant.Complexity.PolyTime ea.toFinEncoding eb.toFinEncoding f where
  toTM2ComputableInPolyTime := PlanarHom.FiniteReachableAlphabetMachines.restrictComputer h
  finiteAlphabets := PlanarHom.FiniteReachableAlphabetMachines.alphabetFintype h

@[simp] theorem finiteComputer_time {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β}
    {f : α → β} (h : TM2ComputableInPolyTime ea.encode eb.encode f) :
    (finiteComputer h).time = h.time := rfl

@[simp] theorem finiteComputer_steps {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β}
    {f : α → β} (h : TM2ComputableInPolyTime ea.encode eb.encode f) (a : α) :
    ((finiteComputer h).outputsFun a).steps = (h.outputsFun a).steps := rfl

/-- FP agrees under the very same input and output codewords. -/
theorem fp_iff_finiteFP {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β) (f : α → β) :
    FP ea eb f ↔ Holant.Complexity.InFP ea.toFinEncoding eb.toFinEncoding f := by
  constructor
  · rintro ⟨h⟩
    exact ⟨finiteComputer h⟩
  · rintro ⟨h⟩
    exact ⟨h.toTM2ComputableInPolyTime⟩

/-- Source certificate counts are exactly the common finite witness counts. -/
theorem certificateCount_eq_countAccepted (p : Polynomial ℕ) (V : Bits × Bits → Bool) (x : Bits) :
    certificateCount p V x =
      Counting.Foundation.countAccepted (fun w : Fin (p.eval x.length) → Bool => V (x, List.ofFn w)) :=
  (Counting.Foundation.countAccepted_eq_card _).symm

/-- The deterministic replay verifier is a finite-alphabet machine on its actual
framed pair input code, with no assumed evaluator or alphabet premise. -/
noncomputable def finiteReplayVerifier (M : PlanarHom.NondeterministicTM2.Machine) :
    Holant.Complexity.PolyTime
      (BitEncoding.bits.prod BitEncoding.bits).toFinEncoding BitEncoding.bool.toFinEncoding
      (PlanarHom.NondeterministicReplayCompiler.verifier M) :=
  finiteComputer (PlanarHom.NondeterministicReplayCompiler.computer M)

end Counting.Bridge.PlanarHomSharpP
