import Counting.Algorithm.KarpLubyRequest.Evaluation.Run
import Counting.Algorithm.KarpLubyRequest.EstimatorEndpoint
import Counting.Algorithm.KarpLubyRequest.TapeBudget.Run

/-!
# The actual evaluator's value on the original decoded request

Dense rows preserve the original ordered clause occurrences. The group loop
uses the original random bits without padding or permutation. Consequently the
actual evaluator's literal rational output is the original total raw evaluator
on every decoded, valid request with the exact tape budget. The positive-mass
gate also bounds both numeric loop counts by physical tape length.
These are semantic and size bridges, with no assumed machine execution.
-/
namespace Counting.Algorithm.KarpLubyRequest.Whole.ValueBridge
open Computability
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine
open Sampling

def originalRows (r : ProgramEncoding.Request) : List RowSemantics.Cells :=
  (DenseNormalization.formula r.problem.variableCount r.problem.formula).value

theorem originalRows_denote (r : ProgramEncoding.Request) :
    (originalRows r).map (DenseNormalization.denote r.problem.variableCount) =
      DNF.normalizeFormula r.problem.formula :=
  DenseNormalization.formula_refines r.problem.formula

theorem originalRows_lengths (r : ProgramEncoding.Request) :
    ∀ row ∈ originalRows r, row.length = r.problem.variableCount :=
  DenseNormalization.formula_lengths r.problem.formula

theorem originalRows_mass (r : ProgramEncoding.Request) :
    TotalMass.rowSum (originalRows r) = Program.totalMass (DNF.normalizeFormula r.problem.formula) := by
  rw [TotalMass.rowSum_original r.problem.variableCount _ (originalRows_lengths r),
    originalRows_denote]

theorem originalRows_width (r : ProgramEncoding.Request) :
    (encodeNat (TotalMass.rowSum (originalRows r))).length =
      dyadicBits (Program.totalMass (DNF.normalizeFormula r.problem.formula)) := by
  rw [SampleBody.width_original r.problem.variableCount _ (originalRows_lengths r),
    originalRows_denote]

theorem originalRows_tape (r : ProgramEncoding.Request)
    (hlen : r.tape.length = Program.requestedBudget r.problem.formula r.epsilon r.delta) :
    r.tape.length = Program.requestedGroups r.delta *
      (Program.requestedSamples (DNF.normalizeFormula r.problem.formula) r.epsilon *
        (encodeNat (TotalMass.rowSum (originalRows r))).length) := by
  rw [originalRows_width]
  exact hlen

/-- Full ordered numerator list and exhausted tape, for the actual loop. -/
theorem original_groupResult (r : ProgramEncoding.Request)
    (hlen : r.tape.length = Program.requestedBudget r.problem.formula r.epsilon r.delta) :
    Evaluation.groupResult r.problem.variableCount (originalRows r)
      (Program.requestedSamples (DNF.normalizeFormula r.problem.formula) r.epsilon)
      (Program.requestedGroups r.delta) r.tape = (EstimatorEndpoint.requestGroups r, []) := by
  unfold Evaluation.groupResult
  rw [originalRows_denote, originalRows_width]
  exact EstimatorEndpoint.request_group_loop r hlen

/-- The equality is between literal output bytes; no canonical-input premise
or replacement decoder is used. -/
theorem output_eq_evalBits (raw : List Bool) (r : ProgramEncoding.Request)
    (hdecode : ProgramEncoding.request.decode raw = some r)
    (hvalid : Program.ValidRequest r.epsilon r.delta)
    (hlen : r.tape.length = Program.requestedBudget r.problem.formula r.epsilon r.delta) :
    Encoding.encodeOutput (Evaluation.resultValue r.problem.variableCount (originalRows r)
      (Program.requestedSamples (DNF.normalizeFormula r.problem.formula) r.epsilon)
      (Program.requestedGroups r.delta) r.tape) = ProgramEncoding.evalBits raw := by
  rw [EstimatorEndpoint.evalBits_requestGroups raw r hdecode hvalid hlen]
  unfold Evaluation.resultValue
  rw [original_groupResult r hlen]

theorem requestedSamples_pos_of_mass {n : ℕ} (cs : List (DNF.Clause n))
    (hm : 0 < Program.totalMass cs) (epsilon : ℚ) :
    0 < Program.requestedSamples cs epsilon := by
  apply samples_pos
  apply List.length_pos_iff.mpr
  intro he
  simp only [he, Program.totalMass_nil] at hm
  omega

theorem requestedGroups_pos (delta : ℚ) : 0 < Program.requestedGroups delta :=
  Nat.mul_pos (by decide) (confidenceGroups_pos delta)

/-- These count bounds use the positive-mass gate and the entire exact tape,
not the binary length of either count. Parameter validity is unnecessary here. -/
theorem requestedCounts_le_tape (r : ProgramEncoding.Request)
    (hm : 0 < Program.totalMass (DNF.normalizeFormula r.problem.formula))
    (hlen : r.tape.length = Program.requestedBudget r.problem.formula r.epsilon r.delta) :
    Program.requestedSamples (DNF.normalizeFormula r.problem.formula) r.epsilon ≤ r.tape.length ∧
      Program.requestedGroups r.delta ≤ r.tape.length := by
  apply TapeBudget.Bank.counts_le_tape _ _ _ r.tape
    (requestedSamples_pos_of_mass _ hm r.epsilon) (requestedGroups_pos r.delta) hm
  exact decide_eq_true hlen

end Counting.Algorithm.KarpLubyRequest.Whole.ValueBridge
