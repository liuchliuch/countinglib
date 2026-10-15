import Counting.Algorithm.KarpLubyRequest.Preparation.AcceptedRun
import Counting.Algorithm.KarpLubyRequest.Preparation.Rejection
import Counting.Algorithm.KarpLubyRequest.Preparation.RawSemantics

/-! Actual execution on every raw request, using the unchanged decoder.
The output specification is only a theorem target; the source program consists
solely of the previously displayed finite stack instructions and source calls. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine
set_option backward.isDefEq.respectTransparency false

def problemResult (p : Encoding.Input) (epsilon delta : ℚ) (tape : List Bool) : List Bool :=
  if Program.totalMass (DNF.normalizeFormula p.formula) = 0 then [false]
  else if decide (tape.length = Program.requestedBudget p.formula epsilon delta) then
    payload (Dense.CellCodec.rows (DenseNormalization.formula p.variableCount p.formula).value)
      (encodeNat (Program.totalMass (DNF.normalizeFormula p.formula)))
      (encodeNat (Program.requestedSamples (DNF.normalizeFormula p.formula) epsilon))
      (encodeNat (Program.requestedGroups delta)) tape
  else [false]

def requestResult (r : ProgramEncoding.Request) : List Bool :=
  if Program.ValidRequest r.epsilon r.delta then problemResult r.problem r.epsilon r.delta r.tape
  else [false]

def rawResult (raw : List Bool) : List Bool :=
  (ProgramEncoding.request.decode raw).elim [false] requestResult

/-- The actual retained-source result agrees with the original dependent
problem and its numerical sample/group and tape-budget conventions. -/
theorem preparedResult_original {raw : List Bool} {source : RequestParser.Stack → List Bool}
    {fields : ProblemHeader.Fields} {r : ProgramEncoding.Request}
    (hs : ParameterValidation.SourceFields source fields)
    (hsep : ProblemHeader.separate raw = some fields)
    (hdecode : ProgramEncoding.request.decode raw = some r)
    (hv : Program.ValidRequest r.epsilon r.delta) (f : Formula source)
    (hp : (⟨(variableWord source).length, f⟩ : Encoding.Input) = r.problem)
    (ht : randomWord source = r.tape) :
    preparedResult source f = problemResult r.problem r.epsilon r.delta r.tape := by
  have hc := RawSemantics.counts_for_formula hs hsep hdecode hv f
  have hm : Sampling.TotalMass.rowSum (normalizedRows source f) =
      Program.totalMass (DNF.normalizeFormula f) := RawSemantics.normalized_mass f
  have hg := RawSemantics.budget_valid hs hsep hdecode hv f hp
  change TapeBudget.Arithmetic.valid (gateInput source f) = _ at hg
  have hsample : (gateInput source f).1 = Program.requestedSamples (DNF.normalizeFormula f) r.epsilon :=
    congrArg (fun q : ℕ × (ℕ × (ℕ × ℕ)) => q.2.2.1) hc
  have hgroup : (gateInput source f).2.1 = Program.requestedGroups r.delta :=
    congrArg (fun q : ℕ × (ℕ × (ℕ × ℕ)) => q.2.2.2) hc
  have hmass : (gateInput source f).2.2.1 = Program.totalMass (DNF.normalizeFormula f) := hm
  simp only [preparedResult, positiveResult, hg, hm, hsample, hgroup, hmass, ht]
  have he := congrArg (fun p : Encoding.Input => problemResult p r.epsilon r.delta r.tape) hp
  have hb := RawSemantics.requestedBudget_eq f r hp
  simpa only [problemResult, hb, normalizedRows] using he

theorem status_true_decode (raw : List Bool) (h : parameterStatus raw = true) :
    ∃ r, ProgramEncoding.request.decode raw = some r ∧ Program.ValidRequest r.epsilon r.delta := by
  cases hd : ProgramEncoding.request.decode raw with
  | none => dsimp only [parameterStatus] at h; rw [hd] at h; contradiction
  | some r =>
    refine ⟨r, rfl, ?_⟩
    dsimp only [parameterStatus] at h
    rw [hd] at h
    exact of_decide_eq_true h

theorem rawResult_rejected (raw : List Bool) (h : parameterStatus raw = false) : rawResult raw = [false] := by
  cases hd : ProgramEncoding.request.decode raw with
  | none => simp only [rawResult, hd, Option.elim_none]
  | some r =>
    have hv : ¬ Program.ValidRequest r.epsilon r.delta := by
      dsimp only [parameterStatus] at h
      rw [hd] at h
      exact of_decide_eq_false h
    simp only [rawResult, hd, Option.elim_some, requestResult, hv, ite_false]

/-- Every raw word executes the actual finite preparation program to a clean
halt with the exact zero/positive intermediate codec. This theorem supplies no
free parser, normalization, arithmetic, transfer, gate or cleanup operation. -/
theorem raw_run (raw : List Bool) :
    ∃ time, RunsExactly computer.step (initList computer raw) (haltList computer (rawResult raw)) time := by
  rw [halt_eq]
  cases hs : parameterStatus raw with
  | false =>
    obtain ⟨time, _, run⟩ := rejected_run raw hs
    rw [rawResult_rejected raw hs]
    exact ⟨time, run⟩
  | true =>
    obtain ⟨r, hd, hv⟩ := status_true_decode raw hs
    obtain ⟨ending, parserTime, _, parserRun, keep⟩ := parameter_call raw
    obtain ⟨source, fields, hfields, hsep, he⟩ := keep r hd hv
    obtain ⟨f, hf, hp, ht⟩ := RawSemantics.decoded_source hfields hsep hd
    rw [hs, he] at parserRun
    obtain ⟨time, _, run⟩ := accepted_run source f hf
    have hout := preparedResult_original hfields hsep hd hv f hp ht
    rw [hout] at run
    have hall := parserRun.trans run
    refine ⟨time + parserTime, ?_⟩
    simpa only [rawResult, hd, Option.elim_some, requestResult, hv, ite_true] using hall

end
end Counting.Algorithm.KarpLubyRequest.Preparation
