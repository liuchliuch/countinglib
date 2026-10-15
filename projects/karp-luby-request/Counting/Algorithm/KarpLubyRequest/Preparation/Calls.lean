import Counting.Algorithm.KarpLubyRequest.Preparation.Bank

/-! Exact calls of the unique source machines in the displayed physical banks.
Each theorem preserves all other banks; the transfer stages separately establish
these source-input configurations by executing ordinary stack instructions.
-/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
open Counting.Algorithm.KarpLuby

set_option backward.isDefEq.respectTransparency false

def parameterStatus (raw : List Bool) : Bool :=
  (ProgramEncoding.request.decode raw).any (fun r => decide (Program.ValidRequest r.epsilon r.delta))

/-- This is the original complete raw decoder and validity check, including its
rejecting executions. No prepared raw-field hypothesis is supplied to the call. -/
theorem parameter_call (raw : List Bool) :
    ∃ ending time, time ≤ ParameterValidation.timeBound raw.length ∧
      RunsExactly computer.step (initList computer raw)
        (configuration .validated
          (none, {initialMemory with parameter := (parameterStatus raw, BinaryArithmetic.Comparison.initial)})
          (parameterData ending)) time ∧
      (∀ r, ProgramEncoding.request.decode raw = some r → Program.ValidRequest r.epsilon r.delta →
        ∃ source f, ParameterValidation.SourceFields source f ∧ ProblemHeader.separate raw = some f ∧
          ending = ParameterValidation.prepared source 4) := by
  obtain ⟨ending, time, bound, run, keep⟩ := ParameterValidation.terminates raw
  refine ⟨ending, time, bound, ?_, keep⟩
  rw [input_eq]
  apply MachineCall.run parameterStacks Label.parameter .validated parameterState
    ParameterProgram.program program parameter_code
    (initialMemory.counts, initialMemory.formula, initialMemory.mass, initialMemory.budget)
    (fun _ => []) (initList ParameterProgram.computer raw)
    (ParameterValidation.finished (parameterStatus raw) ending)
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k
      change wordTape ParameterProgram.computer.k₀ raw k = (initList ParameterProgram.computer raw).stk k
      by_cases hk : k = ParameterProgram.computer.k₀
      · subst k; rfl
      · dsimp only [initList]
        simp only [wordTape, Function.update_apply, hk, ite_false, ↓reduceDIte]
    · intro j h
      rcases j with ((j | j) | (j | (j | (j | j)))) | j <;> first
        | rfl
        | exact (h j rfl).elim
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro j h
      rcases j with ((j | j) | (j | (j | (j | j)))) | j <;> first
        | rfl
        | exact (h j rfl).elim
  · dsimp only [FinTM2.step] at run
    exact run

/-- The complete raw-formula source is called on words physically delivered by
the transfer stages. Original variable/formula words and ordered rows remain. -/
theorem formula_call (d : Data) (memory : Memory) (old : Bool) (original raw : List Bool)
    (f : DNF.Formula original.length)
    (hdecode : (Encoding.formula original.length).decode raw = some f) :
    ∃ bit time, time ≤ Dense.Formula.rawCost original.length raw.length + 1 ∧
      RunsExactly computer.step
        (configuration (.formula .copy)
          (none, {memory with formula := (old, IntegerArithmetic.CarryProtocol.clean (false, false))})
          {d with formula := Dense.Formula.bank original raw [] [] [] [] [] []})
        (configuration (.copyMove .rows)
          (none, {memory with formula := (bit, IntegerArithmetic.CarryProtocol.clean (false, false))})
          {d with formula := (Dense.Formula.outputBank original raw
            (encodeNat (DNF.normalizeFormula f).length)
            (Dense.CellCodec.rows (Counting.Algorithm.KarpLubyMachine.DenseNormalization.formula
              original.length f).value))}) time := by
  obtain ⟨bit, time, bound, run⟩ := Dense.Formula.formula_call old original raw f hdecode
  refine ⟨bit, time, bound, ?_⟩
  apply MachineCall.run formulaStacks Label.formula (.copyMove .rows) formulaState
    Dense.Formula.program program formula_code
    (memory.parameter, memory.counts, memory.mass, memory.budget) d.tapes
    (cfg Dense.Formula.Label.copy (Dense.Formula.cleanMemory old)
      (Dense.Formula.bank original raw [] [] [] [] [] []))
    (Dense.Formula.returned bit original raw (encodeNat (DNF.normalizeFormula f).length)
      (Dense.CellCodec.rows (Counting.Algorithm.KarpLubyMachine.DenseNormalization.formula
        original.length f).value))
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro j h
      rcases j with (j | (j | (j | (j | j)))) | j <;> first
        | rfl
        | exact (h j rfl).elim
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro j h
      rcases j with (j | (j | (j | (j | j)))) | j <;> first
        | rfl
        | exact (h j rfl).elim
  · dsimp only [FinTM2.step] at run
    exact run

/-- The mass source consumes its actual copied row stream. The separate dense
bank survives, and the result is a canonical word on the mass source's output. -/
theorem mass_call (d : Data) (memory : Memory) (rows : List Sampling.RowSemantics.Cells) :
    RunsExactly computer.step
      (configuration (.mass 0) (none, {memory with mass := BinaryArithmetic.Addition.initial})
        {d with mass := Sampling.TotalMass.tapes (Dense.CellCodec.rows rows) [] [] [] [] []})
      (configuration .massCheck (none, {memory with mass := BinaryArithmetic.Addition.initial})
        {d with mass := (Sampling.TotalMass.tapes [] []
          (encodeNat (Sampling.TotalMass.rowSum rows)) [] [] [])})
      (Sampling.TotalMass.runTime rows 0) := by
  apply MachineCall.run massStacks Label.mass .massCheck massState
    Sampling.TotalMass.program program mass_code
    (memory.parameter, memory.counts, memory.formula, memory.budget) d.tapes
    (Sampling.TotalMass.config 0 (Dense.CellCodec.rows rows) [] [] [] [] [])
    (Sampling.TotalMass.finished (encodeNat (Sampling.TotalMass.rowSum rows)))
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro j h
      rcases j with (j | (j | (j | (j | j)))) | j <;> first
        | rfl
        | exact (h j rfl).elim
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro j h
      rcases j with (j | (j | (j | (j | j)))) | j <;> first
        | rfl
        | exact (h j rfl).elim
  · have run := Sampling.TotalMass.run_exact rows 0
    dsimp only [FinTM2.step] at run
    have hz : encodeNat 0 = ([] : List Bool) := rfl
    simpa only [RunsExactly, Nat.zero_add, hz] using run

/-- The shared parameter bank is used in place. The physically copied clause
count drives the original serializer and full binary arithmetic source. -/
theorem counts_call (d : Data) (memory : Memory)
    (source : RequestParser.Stack → List Bool) (m : ℕ) :
    RunsExactly computer.step
      (configuration (.counts (ParameterCountsBank.own 0))
        (none, {memory with counts := ParameterCountsBank.Arithmetic.initial})
        {d with counts := (ParameterCountsBank.ready (ParameterValidation.prepared source 4)
          (encodeNat m) [])})
      (configuration (.dropScan 0)
        (none, {memory with counts := ParameterCountsBank.Arithmetic.initial})
        {d with counts := (ParameterCountsBank.resultTapes (ParameterValidation.prepared source 4)
          (encodeNat m) (ParameterCounts.outputEncoding.encode
            (ParameterCounts.result (ParameterCountsBank.input source m))))})
      (1 + ((ParameterCounts.computes.outputs (ParameterCountsBank.input source m)).steps +
        ParameterCountsBank.serializeTime (ParameterValidation.prepared source 4) (encodeNat m))) := by
  apply MachineCall.run countsStacks Label.counts (.dropScan 0) countsState
    ParameterCountsBank.program program counts_code
    (memory.formula, memory.mass, memory.budget) d.tapes
    (cfg (ParameterCountsBank.own 0) (memory.parameter, ParameterCountsBank.Arithmetic.initial)
      (ParameterCountsBank.ready (ParameterValidation.prepared source 4) (encodeNat m) []))
    (ParameterCountsBank.finished source m memory.parameter)
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro j h
      rcases j with (j | (j | (j | (j | j)))) | j <;> first
        | rfl
        | exact (h j rfl).elim
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro j h
      rcases j with (j | (j | (j | (j | j)))) | j <;> first
        | rfl
        | exact (h j rfl).elim
  · have run := ParameterCountsBank.run source m memory.parameter
    dsimp only [FinTM2.step] at run
    exact run

/-- The exact tape gate sees four physically delivered words. Its arithmetic
work is cleared by the source, while the original four words are retained. -/
theorem budget_call (d : Data) (memory : Memory) (x : TapeBudget.Arithmetic.Input)
    (status : TapeBudget.Bank.Status) :
    RunsExactly computer.step
      (configuration (.budget (TapeBudget.Bank.own 0))
        (none, {memory with budget := (status, TapeBudget.Bank.Engine.initial)})
        {d with budget := TapeBudget.Bank.ready (TapeBudget.Bank.prepared x) []})
      (configuration .gated
        (none, {memory with budget := (TapeBudget.Bank.outcome x, TapeBudget.Bank.Engine.initial)})
        {d with budget := TapeBudget.Bank.ready (TapeBudget.Bank.prepared x) []})
      (TapeBudget.Bank.steps x) := by
  apply MachineCall.run budgetStacks Label.budget .gated budgetState
    TapeBudget.Bank.program program budget_code
    (memory.parameter, memory.counts, memory.formula, memory.mass) d.tapes
    (cfg (TapeBudget.Bank.own 0) (status, TapeBudget.Bank.Engine.initial)
      (TapeBudget.Bank.ready (TapeBudget.Bank.prepared x) []))
    (TapeBudget.Bank.finished (TapeBudget.Bank.prepared x)
      (TapeBudget.Bank.outcome x).1 (TapeBudget.Bank.outcome x).2)
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro j h
      rcases j with (j | (j | (j | (j | j)))) | j <;> first
        | rfl
        | exact (h j rfl).elim
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro j h
      rcases j with (j | (j | (j | (j | j)))) | j <;> first
        | rfl
        | exact (h j rfl).elim
  · have run := TapeBudget.Bank.run x status
    dsimp only [FinTM2.step] at run
    exact run

end
end Counting.Algorithm.KarpLubyRequest.Preparation
