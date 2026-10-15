/- Extracted concrete finite-machine foundation; see docs/BELL_LIST_MACHINES_REUSE.json. -/
import Paper2.Complexity.BellMachines.GraphPreprocessing.Frame
namespace Paper2.Complexity.BellMachines.MoveWord
open Turing Computability Paper2.Complexity StackProtocol
variable {K Λ τ : Type} [DecidableEq K]
/-- Order-preserving destructive transfer with an arbitrary retained caller frame. -/
theorem move_exact (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (move restore good : Λ)
    (hm : ExecutesAt step move (copyMoveStmt src tmp move restore))
    (hr : ExecutesAt step restore (copyMoveStmt tmp dst restore good))
    (memory : τ) (frame : K → List Bool) (word suffix : List Bool) :
    RunsExactly step (cfg move memory (tapes3 frame src dst tmp word suffix []))
      (cfg good memory (tapes3 frame src dst tmp [] (word ++ suffix) []))
      (2 * (word.length + 1)) := by
  have first := copy_move_exact src dst tmp hsd hst step move restore hm memory frame word suffix []
  have last := GraphPreprocessing.Frame.restore_exact src dst tmp hdt step restore good hr
    memory frame [] suffix word.reverse
  simp only [List.append_nil] at first
  simpa [Nat.two_mul] using first.trans last


end Paper2.Complexity.BellMachines.MoveWord
