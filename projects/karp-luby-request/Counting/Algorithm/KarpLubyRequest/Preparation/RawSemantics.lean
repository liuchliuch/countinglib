import Counting.Algorithm.KarpLubyRequest.Preparation.DenseInput
import Counting.Algorithm.KarpLubyRequest.Dense.FormulaCall
import Counting.Algorithm.KarpLubyRequest.Sampling.TotalMassRun
import Counting.Algorithm.KarpLubyRequest.TapeBudget.Arithmetic

/-!
# Retained raw request fields and the original numerical parameters

These bridges consume the actual parser's retained-field relation and the
unchanged request decoder. Variable words may contain either bit value and
rational words need not be canonical. The dependent problem equality retains
the original formula and its ambient variable count together. Normalization,
mass computation, parameter arithmetic and the tape gate are existing providers;
no semantic function below is a machine instruction or an execution premise.
-/
namespace Counting.Algorithm.KarpLubyRequest.Preparation.RawSemantics
open Computability Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

theorem variableWord_eq {source : RequestParser.Stack → List Bool} {fields : ProblemHeader.Fields}
    (hs : ParameterValidation.SourceFields source fields) :
    variableWord source = fields.variableWord :=
  (hs ProblemHeader.destination).trans (RequestParser.output_variables fields)

theorem formulaWord_eq {source : RequestParser.Stack → List Bool} {fields : ProblemHeader.Fields}
    (hs : ParameterValidation.SourceFields source fields) :
    formulaWord source = fields.formula :=
  (hs ProblemHeader.source).trans (RequestParser.output_source fields)

theorem randomWord_eq {source : RequestParser.Stack → List Bool} {fields : ProblemHeader.Fields}
    (hs : ParameterValidation.SourceFields source fields) :
    randomWord source = fields.tape := by
  exact hs (.inl 0)

/-- Successful raw decoding identifies all data, including the dependent
formula, rather than merely establishing that some formula was accepted. -/
theorem decoded_header {raw : List Bool} {fields : ProblemHeader.Fields}
    {r : ProgramEncoding.Request}
    (hsep : ProblemHeader.separate raw = some fields)
    (hdecode : ProgramEncoding.request.decode raw = some r) :
    ∃ f : DNF.Formula fields.variableWord.length,
      (Encoding.formula fields.variableWord.length).decode fields.formula = some f ∧
      (⟨fields.variableWord.length, f⟩ : Encoding.Input) = r.problem ∧
      fields.tape = r.tape ∧
      RationalFields.value fields.epsilon = r.epsilon ∧
      RationalFields.value fields.delta = r.delta := by
  have hv := ProblemHeader.decode_eq raw
  rw [hsep, Option.bind_some, hdecode] at hv
  cases hd : (Encoding.formula fields.variableWord.length).decode fields.formula with
  | none =>
    simp only [ProblemHeader.validate, hd] at hv
    change (none : Option ProgramEncoding.Request) = some r at hv
    cases hv
  | some f =>
    simp only [ProblemHeader.validate, hd, Option.bind_some] at hv
    have he : (⟨⟨fields.variableWord.length, f⟩, RationalFields.value fields.epsilon,
        RationalFields.value fields.delta, fields.tape⟩ : ProgramEncoding.Request) = r :=
      Option.some.inj hv
    cases he
    exact ⟨f, rfl, rfl, rfl, rfl, rfl⟩

/-- The formula consumed by the dense source program is the original parsed
problem, with its physical unary header's length as the ambient type index. -/
theorem decoded_source {raw : List Bool} {source : RequestParser.Stack → List Bool}
    {fields : ProblemHeader.Fields} {r : ProgramEncoding.Request}
    (hs : ParameterValidation.SourceFields source fields)
    (hsep : ProblemHeader.separate raw = some fields)
    (hdecode : ProgramEncoding.request.decode raw = some r) :
    ∃ f : DNF.Formula (variableWord source).length,
      (Encoding.formula (variableWord source).length).decode (formulaWord source) = some f ∧
      (⟨(variableWord source).length, f⟩ : Encoding.Input) = r.problem ∧
      randomWord source = r.tape := by
  rw [variableWord_eq hs, formulaWord_eq hs, randomWord_eq hs]
  obtain ⟨f, hf, hp, ht, _, _⟩ := decoded_header hsep hdecode
  exact ⟨f, hf, hp, ht⟩

theorem normalized_rows {n : ℕ} (f : DNF.Formula n) :
    (DenseNormalization.formula n f).value.map (DenseNormalization.denote n) =
      DNF.normalizeFormula f := DenseNormalization.formula_refines f

theorem normalized_lengths {n : ℕ} (f : DNF.Formula n) :
    ∀ row ∈ (DenseNormalization.formula n f).value, row.length = n :=
  DenseNormalization.formula_lengths f

theorem normalized_count {n : ℕ} (f : DNF.Formula n) :
    (DenseNormalization.formula n f).value.length = (DNF.normalizeFormula f).length :=
  Dense.Formula.normalized_count f

/-- The physical row accumulator sums exactly the original tagged clause mass,
including repeated clauses, free coordinates and nullary clauses. -/
theorem normalized_mass {n : ℕ} (f : DNF.Formula n) :
    Sampling.TotalMass.rowSum (DenseNormalization.formula n f).value =
      Program.totalMass (DNF.normalizeFormula f) := by
  rw [Sampling.TotalMass.rowSum_original n _ (DenseNormalization.formula_lengths f),
    DenseNormalization.formula_refines]

/-- No normalization of the retained rational words is assumed: the original
raw components feed the actual binary division and subsequent arithmetic. -/
theorem counts_result {raw : List Bool} {source : RequestParser.Stack → List Bool}
    {fields : ProblemHeader.Fields} {r : ProgramEncoding.Request}
    (hs : ParameterValidation.SourceFields source fields)
    (hsep : ProblemHeader.separate raw = some fields)
    (hdecode : ProgramEncoding.request.decode raw = some r)
    (hv : Program.ValidRequest r.epsilon r.delta) (m : ℕ) :
    ParameterCounts.result (ParameterCountsBank.input source m) =
      (reciprocalCeiling r.epsilon, reciprocalCeiling r.delta,
        samples m r.epsilon, Program.requestedGroups r.delta) := by
  obtain ⟨_, _, _, _, he, hd⟩ := decoded_header hsep hdecode
  obtain ⟨hdenE, hdenD, _⟩ := ParameterValidation.parsed_parameter_bounds hsep
  have huE : ParameterSemantics.unsigned fields.epsilon :=
    (ParameterSemantics.positive_iff fields.epsilon hdenE).mp (by rw [he]; exact hv.1)
  have huD : ParameterSemantics.unsigned fields.delta :=
    (ParameterSemantics.positive_iff fields.delta hdenD).mp (by rw [hd]; exact hv.2.2.1)
  rw [ParameterCountsBank.input_fields hs]
  simpa only [he, hd] using
    ParameterCounts.result_fields fields.epsilon fields.delta m hdenE hdenD huE huD

theorem counts_for_formula {raw : List Bool} {source : RequestParser.Stack → List Bool}
    {fields : ProblemHeader.Fields} {r : ProgramEncoding.Request}
    (hs : ParameterValidation.SourceFields source fields)
    (hsep : ProblemHeader.separate raw = some fields)
    (hdecode : ProgramEncoding.request.decode raw = some r)
    (hv : Program.ValidRequest r.epsilon r.delta) {n : ℕ} (f : DNF.Formula n) :
    ParameterCounts.result (ParameterCountsBank.input source (DNF.normalizeFormula f).length) =
      (reciprocalCeiling r.epsilon, reciprocalCeiling r.delta,
        Program.requestedSamples (DNF.normalizeFormula f) r.epsilon,
        Program.requestedGroups r.delta) :=
  counts_result hs hsep hdecode hv _

/-- Dependent transport is through the whole original problem record. -/
theorem requestedBudget_eq {n : ℕ} (f : DNF.Formula n) (r : ProgramEncoding.Request)
    (hp : (⟨n, f⟩ : Encoding.Input) = r.problem) :
    Program.requestedBudget f r.epsilon r.delta =
      Program.requestedBudget r.problem.formula r.epsilon r.delta :=
  congrArg (fun p : Encoding.Input => Program.requestedBudget p.formula r.epsilon r.delta) hp

/-- The actual budget machine's Boolean comparison is precisely the original
request's equality gate. In particular it does not accept a padded extra suffix. -/
theorem budget_valid {raw : List Bool} {source : RequestParser.Stack → List Bool}
    {fields : ProblemHeader.Fields} {r : ProgramEncoding.Request}
    (hs : ParameterValidation.SourceFields source fields)
    (hsep : ProblemHeader.separate raw = some fields)
    (hdecode : ProgramEncoding.request.decode raw = some r)
    (hv : Program.ValidRequest r.epsilon r.delta) {n : ℕ} (f : DNF.Formula n)
    (hp : (⟨n, f⟩ : Encoding.Input) = r.problem) :
    let counts := ParameterCounts.result
      (ParameterCountsBank.input source (DNF.normalizeFormula f).length)
    TapeBudget.Arithmetic.valid (counts.2.2.1, counts.2.2.2,
      Sampling.TotalMass.rowSum (DenseNormalization.formula n f).value, randomWord source) =
      decide (r.tape.length = Program.requestedBudget r.problem.formula r.epsilon r.delta) := by
  dsimp only
  rw [counts_for_formula hs hsep hdecode hv f]
  obtain ⟨_, _, _, ht, _, _⟩ := decoded_header hsep hdecode
  rw [normalized_mass, randomWord_eq hs, ht]
  change decide (r.tape.length = Program.requestedBudget f r.epsilon r.delta) = _
  rw [requestedBudget_eq f r hp]

end Counting.Algorithm.KarpLubyRequest.Preparation.RawSemantics
