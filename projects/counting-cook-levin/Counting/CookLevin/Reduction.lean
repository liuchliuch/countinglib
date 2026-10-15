import Counting.CookLevin.Compiler
import Counting.CookLevin.Membership
import Counting.Complexity.Reduction
import PlanarHom.SingleTapeSharpPBridge

/-! Public parsimonious completeness for the independent encoded NOR target. -/
noncomputable section
namespace Counting.CookLevin
open PlanarHom.Complexity PlanarHom.SingleTapeNondeterministic

/-- A real finite polynomial-time machine emits every independent target field. -/
def machineReduction (M : PolynomialMachine) :
    Counting.Complexity.ParsimoniousReduction (Computability.encodingList Bool)
      Instance.encoding.toFinEncoding M.count Instance.count where
  map := compile M
  machine := compiler M
  correct := compile_count M

/-- Every standard-bit public #P function reduces parsimoniously to the same
independent NOR target; its evaluator and encoding contain no source machine. -/
theorem sharpP_reduces {f : Bits → ℕ}
    (hf : Counting.Complexity.InSharpP (Computability.encodingList Bool) f) :
    Counting.Complexity.ParsimoniousReduces (Computability.encodingList Bool)
      Instance.encoding.toFinEncoding f Instance.count := by
  have h := (Counting.Bridge.WitnessSharpP.bits_inSharpP_iff_acceptingPaths f).mp hf
  obtain ⟨M, hM⟩ := h.singleTapeSharpP
  exact ⟨(machineReduction M).congr hM (fun _ => rfl)⟩

end Counting.CookLevin
