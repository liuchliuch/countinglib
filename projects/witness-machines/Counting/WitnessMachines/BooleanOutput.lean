import Counting.WitnessMachines.MappedReverse
import PlanarHom.Complexity

set_option backward.isDefEq.respectTransparency false

/-! Actual singleton-output transducers. Both use a two-stack finite program,
consume the input, reset their register, and produce the strict tagged/binary
halt-list result in two transitions. -/
namespace Counting.WitnessMachines.BooleanOutput
open Turing Computability Counting.Computation PlanarHom.Complexity

abbrev Tag := Bool ⊕ Bool

noncomputable def toTagged :
    PolyTime BitEncoding.bool.toFinEncoding (Holant.Complexity.taggedBoolEncoding Bool) id where
  tm := MappedReverse.machine (Sum.inr : Bool → Tag)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun b := by
    have h := MappedReverse.outputs (Sum.inr : Bool → Tag) [b]
    refine { steps := h.steps, evals_in_steps := ?_, steps_le_m := ?_ }
    · simp only [Equiv.refl, List.map_id]
      exact h.evals_in_steps
    · simpa [BitEncoding.toFinEncoding, BitEncoding.bool] using h.steps_le_m
  finiteAlphabets := MappedReverse.alphabetFintype _

noncomputable def fromTagged :
    PolyTime (Holant.Complexity.taggedBoolEncoding Bool) BitEncoding.bool.toFinEncoding id where
  tm := MappedReverse.machine (fun a : Tag => a.elim id id)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun b := by
    have h := MappedReverse.outputs (fun a : Tag => a.elim id id) [Sum.inr b]
    refine { steps := h.steps, evals_in_steps := ?_, steps_le_m := ?_ }
    · simp only [Equiv.refl, List.map_id]
      exact h.evals_in_steps
    · simpa [Holant.Complexity.taggedBoolEncoding] using h.steps_le_m
  finiteAlphabets := MappedReverse.alphabetFintype _

end Counting.WitnessMachines.BooleanOutput
