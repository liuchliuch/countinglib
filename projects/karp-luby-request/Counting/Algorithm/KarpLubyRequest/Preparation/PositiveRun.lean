import Counting.Algorithm.KarpLubyRequest.Preparation.NormalizeRun
import Counting.Algorithm.KarpLubyRequest.Preparation.CountRun
import Counting.Algorithm.KarpLubyRequest.Preparation.Finish

/-! Actual positive-mass arithmetic and gate pipeline. Each intermediate bank
is produced by the preceding source run: clause-copy, count arithmetic, tuple
unframing, mass/tape copies, and the complete binary tape-budget machine. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

abbrev Formula (source : RequestParser.Stack → List Bool) := DNF.Formula (variableWord source).length

def clauseCount (source : RequestParser.Stack → List Bool) (f : Formula source) : ℕ :=
  (DNF.normalizeFormula f).length

def gateInput (source : RequestParser.Stack → List Bool) (f : Formula source) : TapeBudget.Arithmetic.Input :=
  ((countValue source (clauseCount source f)).2.2.1,
    (countValue source (clauseCount source f)).2.2.2,
    Sampling.TotalMass.rowSum (normalizedRows source f), randomWord source)

def extractedCounts (source : RequestParser.Stack → List Bool) (f : Formula source) : Data :=
  extractedData (countResult (normalizedData source f) source (clauseCount source f))
    (encodeNat (gateInput source f).1) (encodeNat (gateInput source f).2.1)

def gatedData (source : RequestParser.Stack → List Bool) (f : Formula source) : Data :=
  {extractedCounts source f with budget := (TapeBudget.Bank.ready (TapeBudget.Bank.prepared (gateInput source f)) [])}

def gatedMemory (source : RequestParser.Stack → List Bool) (f : Formula source) (bit : Bool) : Memory :=
  {workingMemory bit with budget := (TapeBudget.Bank.outcome (gateInput source f), TapeBudget.Bank.Engine.initial)}

def positivePrefixTime (source : RequestParser.Stack → List Bool) (f : Formula source) : ℕ :=
  let m := clauseCount source f
  (TapeBudget.Bank.steps (gateInput source f)) +
    (2 * ((encodeNat (gateInput source f).2.2.1).length + (randomWord source).length) + 4) +
    tupleCost source m +
    (1 + ((ParameterCounts.computes.outputs (ParameterCountsBank.input source m)).steps +
      ParameterCountsBank.serializeTime (ParameterValidation.prepared source 4) (encodeNat m))) +
    (2 * (encodeNat m).length + 2)

/-- Complete physical count/gate prefix, starting directly at the retained
normalization/mass endpoint. No prepared source bank is assumed at a call site. -/
theorem positive_prefix (source : RequestParser.Stack → List Bool) (f : Formula source) (bit : Bool) :
    RunsExactly computer.step
      (configuration (.copyMove .clauses) (none, workingMemory bit) (normalizedData source f))
      (configuration .gated (none, gatedMemory source f bit) (gatedData source f))
      (positivePrefixTime source f) := by
  let m := clauseCount source f
  let d := normalizedData source f
  let x := gateInput source f
  have hcopy := count_input_copy source d (workingMemory bit) m rfl rfl rfl
  have hcounts := counts_call d (workingMemory bit) source m
  have hextract := extract_count_result d source m (workingMemory bit) rfl rfl
  have hbudgetcopy := budget_input_copy (extractedCounts source f) (workingMemory bit)
    (encodeNat x.1) (encodeNat x.2.1) (encodeNat x.2.2.1) (randomWord source) rfl rfl rfl rfl
  have hbudget := budget_call (extractedCounts source f) (workingMemory bit) x (false, false)
  have run := (((hcopy.trans hcounts).trans hextract).trans hbudgetcopy).trans hbudget
  convert run using 1 <;> first | rfl | skip
  dsimp only [positivePrefixTime, m, x]
  omega

/-- Exact semantic value of the agreed intermediate codec. A false gate emits
only the zero tag; a true gate retains canonical binary counts and every
original random bit. -/
def positiveResult (source : RequestParser.Stack → List Bool) (f : Formula source) : List Bool :=
  if TapeBudget.Arithmetic.valid (gateInput source f) then
    payload (Dense.CellCodec.rows (normalizedRows source f))
      (encodeNat (gateInput source f).2.2.1) (encodeNat (gateInput source f).1)
      (encodeNat (gateInput source f).2.1) (randomWord source)
  else [false]

/-- Finish from the actual gate endpoint, with costs charged to all retained
physical words rather than just the output payload. -/
theorem finish_gate (source : RequestParser.Stack → List Bool) (f : Formula source) (bit : Bool) :
    ∃ time, time ≤ 1 + max (finishBound (stackSize (gatedData source f).tapes))
        (stackSize (gatedData source f).tapes + workCount + 3) ∧
      RunsExactly computer.step (configuration .gated (none, gatedMemory source f bit) (gatedData source f))
        (finalConfiguration (positiveResult source f)) time := by
  cases hv : TapeBudget.Arithmetic.valid (gateInput source f) with
  | false =>
    have hflag : (gatedMemory source f bit).budget.1.1 = false := hv
    have hd := gate_false (gatedMemory source f bit) (gatedData source f).tapes hflag
    obtain ⟨time, bound, run⟩ := zero_finish_bound (gatedMemory source f bit) (gatedData source f).tapes rfl
    refine ⟨time + 1, ?_, ?_⟩
    · have hm := Nat.le_max_right (finishBound (stackSize (gatedData source f).tapes))
        (stackSize (gatedData source f).tapes + workCount + 3)
      simpa only [Nat.add_comm] using Nat.add_le_add_left (bound.trans hm) 1
    · have he : positiveResult source f = [false] := by rw [positiveResult, hv]; rfl
      rw [he]
      exact hd.trans run
  | true =>
    have hflag : (gatedMemory source f bit).budget.1.1 = true := hv
    have hd := gate_true (gatedMemory source f bit) (gatedData source f).tapes hflag
    obtain ⟨time, bound, run⟩ := positive_payload (gatedMemory source f bit) (gatedData source f).tapes rfl rfl
    refine ⟨time + 1, ?_, ?_⟩
    · have hm := Nat.le_max_left (finishBound (stackSize (gatedData source f).tapes))
        (stackSize (gatedData source f).tapes + workCount + 3)
      simpa only [Nat.add_comm] using Nat.add_le_add_left (bound.trans hm) 1
    · have hout : payload ((gatedData source f).tapes (formulaStacks 12))
          ((gatedData source f).tapes (budgetOriginal 2))
          ((gatedData source f).tapes (budgetOriginal 0))
          ((gatedData source f).tapes (budgetOriginal 1))
          ((gatedData source f).tapes (budgetOriginal 3)) = positiveResult source f := by
        rw [positiveResult, hv]
        rfl
      rw [hout] at run
      exact hd.trans run

end
end Counting.Algorithm.KarpLubyRequest.Preparation
