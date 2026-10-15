import Counting.Algorithm.KarpLubyRequest.Evaluation.Groups
import Counting.Algorithm.KarpLubyRequest.Evaluation.FinishTail
import Counting.Algorithm.KarpLubyRequest.Evaluation.Zero

/-!
# A single actual evaluator for the prepared request payload

The two physical sample/group loops, their materialized numerator list, the
natural upper median, rational normalization and literal output serialization
are one execution of `Evaluation.program`. Only the decoder/preparation stage
is outside this theorem. The time below charges every stage in that program.
-/
namespace Counting.Algorithm.KarpLubyRequest.Evaluation
open Turing Computability Holant.Complexity StackProtocol BinaryCompose GraphPreprocessing
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine
open Sampling
set_option backward.isDefEq.respectTransparency false

def resultValue (n : ℕ) (rows : List RowSemantics.Cells) (s g : ℕ) (tape : List Bool) : ℚ :=
  (Median.value (groupResult n rows s g tape).1 : ℚ) / s

def timeBound (n : ℕ) (rows : List RowSemantics.Cells) (s g : ℕ) (tape : List Bool) : ℕ :=
  let xs := (groupResult n rows s g tape).1
  groupPhaseTime n rows s g tape + ((Median.input xs).length + 4) + 1 +
    Median.timeBound (Median.input xs).length +
    tailTime (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)) (Median.value xs) s

/-- The complete deterministic source accepts all zero/count/tie boundaries.
The caller supplies exactly the physical tape used by the nested loops. -/
theorem prepared_run (n : ℕ) (rows : List RowSemantics.Cells)
    (hrows : ∀ row ∈ rows, row.length = n) (s g : ℕ) (tape : List Bool)
    (hlen : tape.length = g*(s*(encodeNat (TotalMass.rowSum rows)).length)) :
    ∃ time, time ≤ timeBound n rows s g tape ∧
      RunsExactly computer.step
        (initList computer (payload (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
          (encodeNat s) (encodeNat g) tape))
        (haltList computer (Encoding.encodeOutput (resultValue n rows s g tape))) time := by
  let xs := (groupResult n rows s g tape).1
  let r := Dense.CellCodec.rows rows
  let m := encodeNat (TotalMass.rowSum rows)
  let base : Data := {fields := fieldWords r m (encodeNat s) [] [] []}
  have h0 := group_phase n rows hrows s g tape hlen
  have h1 := group_finish (fun _ => []) initial.2 r m (encodeNat s) xs
  have h2 := runsExactly_one (median_start initial (medianInputData (fun _ => []) r m (encodeNat s) xs))
  obtain ⟨selected, lastFlag, time, ht, h3⟩ := median_call base
    (none, initial.2.1, initial.2.2.2) xs
  rw [median_initial_tapes] at h3
  change RunsExactly computer.step
    (configuration (.median Median.Program.computer.main) initial
      (medianInputData (fun _ => []) r m (encodeNat s) xs))
    (configuration .numMove
      (none, initial.2.1, (none, Median.Program.memory selected lastFlag), initial.2.2.2)
      (tailData r m (Median.value xs) s)) time at h3
  have h4 := finish_tail
    (initial.2.1, (none, Median.Program.memory selected lastFlag), initial.2.2.2)
    r m (Median.value xs) s
  have run := (((h0.trans h1).trans h2).trans h3).trans h4
  rw [← halt_eq] at run
  refine ⟨_, ?_, run⟩
  dsimp only [timeBound]
  change tailTime r m (Median.value xs) s +
    (time + (1 + ((Median.input xs).length+4 + groupPhaseTime n rows s g tape))) ≤ _
  dsimp only [xs, r, m] at ht ⊢
  omega

/-- The primitive interpreter follows the same final execution, not a logical
operation counter. Its fixed syntactic budget is a constant of this program. -/
theorem prepared_bit_cost (n : ℕ) (rows : List RowSemantics.Cells)
    (hrows : ∀ row ∈ rows, row.length = n) (s g : ℕ) (tape : List Bool)
    (hlen : tape.length = g*(s*(encodeNat (TotalMass.rowSum rows)).length)) :
    ∃ time, time ≤ timeBound n rows s g tape ∧
      (Primitive.run program time (some (initList computer
        (payload (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
          (encodeNat s) (encodeNat g) tape)))).2 =
        some (haltList computer (Encoding.encodeOutput (resultValue n rows s g tape))) ∧
      (Primitive.run program time (some (initList computer
        (payload (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
          (encodeNat s) (encodeNat g) tape)))).1 ≤
        machine.primitiveBudget * timeBound n rows s g tape := by
  obtain ⟨time, ht, hr⟩ := prepared_run n rows hrows s g tape hlen
  have h := Primitive.execution_cost program machine.primitiveBudget machine.program_budget_le time _ _ hr
  exact ⟨time, ht, h.1, h.2.trans (Nat.mul_le_mul_left _ ht)⟩

end Counting.Algorithm.KarpLubyRequest.Evaluation
