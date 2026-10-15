import ComplexCSP.Complexity.CSPCountBits
import PlanarHom.ListDedupMachines

/-! # Bit-polynomial comparison of canonically encoded runtime labels

A BitEncoding has a left inverse and therefore unique canonical codewords.
The machine compares these literal words. It does not execute the encoding or
an abstract equality oracle at runtime. This applies to normalized fixed-field
row labels, whose entries vary with the input.
-/
namespace ComplexCSP.ComplexityEncodedEquality
open PlanarHom PlanarHom.Complexity
variable {A : Type} [DecidableEq A]

def equal (p : A × A) : Bool := decide (p.1 = p.2)

theorem fp_equal (e : BitEncoding A) : FP (e.prod e) BitEncoding.bool equal := by
  have hw : FP (e.prod e) (BitEncoding.bits.prod BitEncoding.bits)
      (fun p => (e.encode p.1,e.encode p.2)) := fp_code_view _ _ _ (fun _ => rfl)
  apply (hw.comp ComplexityCSPCountBits.fp_bitsEqual).congr
  intro p
  apply Bool.eq_iff_iff.mpr
  simp only [ComplexityCSPCountBits.bitsEqual, equal, decide_eq_true_eq, Function.comp_apply]
  exact e.injective.eq_iff

/-- Stable runtime deduplication of labels; the output is a sublist of the input. -/
def dedup (xs : List A) : List A := ListDedupMachines.dedup equal xs

theorem fp_dedup (e : BitEncoding A) : FP e.list e.list (dedup : List A → List A) :=
  ListDedupMachines.fp_dedup e equal (fp_equal e)

theorem dedup_sublist (xs : List A) : (dedup xs).Sublist xs :=
  ListDedupMachines.dedup_sublist equal xs

end ComplexCSP.ComplexityEncodedEquality
