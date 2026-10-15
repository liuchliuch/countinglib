import Counting.Algorithm.KarpLubyRequest.Contract
import Counting.Algorithm.KarpLubyRequest.Median.Semantics
import Counting.Algorithm.KarpLubyRequest.Sampling.TapeIterationSpec

/-!
# Materialized group numerators and the original raw evaluator

The physical group loop preserves the order and multiplicity of its observations.
Selecting their natural upper median and dividing once by the sample count gives
the exact original rational output bytes. The raw word may use any representation
accepted by the original decoder; no canonical-input premise is introduced.
These are value and tape equations, not an assumed machine or a cost certificate.
-/
namespace Counting.Algorithm.KarpLubyRequest.EstimatorEndpoint
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

/-- The original finite family, materialized in group order. -/
def groupNumerators {n : ℕ} (cs : List (DNF.Clause n)) (samples groups width : ℕ)
    (tape : CoinTape (groups * (samples * width))) : List ℕ :=
  List.ofFn fun i : Fin groups =>
    (NumeratorMedian.groupNumeratorWithWidth cs samples width
      (Program.coinChunk (width := samples * width) tape i)).value

/-- The stack-machine selector agrees with the existing estimator's numerator,
including zero groups, zero samples, ties and repeated observations. -/
theorem median_groupNumerators {n : ℕ} (cs : List (DNF.Clause n))
    (samples groups width : ℕ) (tape : CoinTape (groups * (samples * width))) :
    Median.value (groupNumerators cs samples groups width tape) =
      (NumeratorMedian.estimateWithWidth cs samples groups width tape).value := by
  rw [groupNumerators, Median.value_ofFn]
  simp only [NumeratorMedian.estimateWithWidth, MedianCost.cacheVector_value]

/-- Total list access matches the existing structured-request adapter. The exact
tape-length gate below ensures that no default bit is read on accepted requests. -/
def requestGroups (r : ProgramEncoding.Request) : List ℕ :=
  groupNumerators (DNF.normalizeFormula r.problem.formula)
    (Program.requestedSamples (DNF.normalizeFormula r.problem.formula) r.epsilon)
    (Program.requestedGroups r.delta)
    (dyadicBits (Program.totalMass (DNF.normalizeFormula r.problem.formula)))
    (fun i => r.tape[i.val]?.getD false)

/-- Accepted tape bytes are exactly the finite tape used by the old evaluator. -/
theorem request_tape (r : ProgramEncoding.Request)
    (hlen : r.tape.length = Program.requestedBudget r.problem.formula r.epsilon r.delta) :
    List.ofFn (fun i : Fin (Program.requestedBudget r.problem.formula r.epsilon r.delta) =>
      r.tape[i.val]?.getD false) = r.tape := by
  apply List.ext_getElem (by simpa only [List.length_ofFn] using hlen.symm)
  intro i hi hi'
  simp only [List.getElem_ofFn, List.getElem?_eq_getElem hi', Option.getD_some]

/-- The original raw tape is exhausted by precisely the requested nested loops.
This is independent of the numerical validity of the accuracy parameters. -/
theorem request_group_loop (r : ProgramEncoding.Request)
    (hlen : r.tape.length = Program.requestedBudget r.problem.formula r.epsilon r.delta) :
    (Sampling.TapeIterationSpec.groupStep (DNF.normalizeFormula r.problem.formula)
      (Program.requestedSamples (DNF.normalizeFormula r.problem.formula) r.epsilon)
      (dyadicBits (Program.totalMass (DNF.normalizeFormula r.problem.formula))))^[
        Program.requestedGroups r.delta] ([], r.tape) = (requestGroups r, []) := by
  have h := Sampling.TapeIterationSpec.group_iterate
    (DNF.normalizeFormula r.problem.formula)
    (Program.requestedSamples (DNF.normalizeFormula r.problem.formula) r.epsilon)
    (dyadicBits (Program.totalMass (DNF.normalizeFormula r.problem.formula)))
    (Program.requestedGroups r.delta) []
    (fun i => r.tape[i.val]?.getD false) []
  have htape := request_tape r hlen
  dsimp only [Program.requestedBudget, Program.randomBitBudget] at htape
  simpa only [List.append_nil, List.nil_append, htape,
    requestGroups, groupNumerators] using h

set_option maxHeartbeats 800000 in
/-- Exact output bytes for every successfully decoded and accepted raw request.
The actual numerator-list, median and fraction machines can use this endpoint. -/
theorem evalBits_requestGroups (raw : List Bool) (r : ProgramEncoding.Request)
    (hr : ProgramEncoding.request.decode raw = some r)
    (hvalid : Program.ValidRequest r.epsilon r.delta)
    (hlen : r.tape.length = Program.requestedBudget r.problem.formula r.epsilon r.delta) :
    ProgramEncoding.evalBits raw = Encoding.encodeOutput
      ((Median.value (requestGroups r) : ℚ) /
        Program.requestedSamples (DNF.normalizeFormula r.problem.formula) r.epsilon) := by
  have he : ProgramEncoding.evalRequest r =
      Program.estimate (DNF.normalizeFormula r.problem.formula)
        (Program.requestedSamples (DNF.normalizeFormula r.problem.formula) r.epsilon)
        (Program.requestedGroups r.delta) (fun i => r.tape[i.val]?.getD false) := by
    rw [ProgramEncoding.evalRequest, ite_eq_left hvalid, dite_eq_left hlen]
    unfold Program.run
    apply congrArg (Program.estimate (DNF.normalizeFormula r.problem.formula)
      (Program.requestedSamples (DNF.normalizeFormula r.problem.formula) r.epsilon)
      (Program.requestedGroups r.delta))
    funext i
    have hi : i.val < r.tape.length := by rw [hlen]; exact i.isLt
    simp only [List.getElem?_eq_getElem hi, Option.getD_some]
  simp only [ProgramEncoding.evalBits, hr]
  rw [he, NumeratorMedian.estimateWithWidth_refines]
  rw [requestGroups, median_groupNumerators]
  rfl

end Counting.Algorithm.KarpLubyRequest.EstimatorEndpoint
