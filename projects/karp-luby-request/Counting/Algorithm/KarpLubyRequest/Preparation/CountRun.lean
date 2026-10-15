import Counting.Algorithm.KarpLubyRequest.Preparation.CountInput
import Counting.Algorithm.KarpLubyRequest.Preparation.Tuple
import Counting.Algorithm.KarpLubyRequest.Preparation.BudgetInput

/-! Real count arithmetic followed by destructive tuple extraction. Retained
raw parameter fields and the canonical clause word survive; the four numeric
results themselves are never installed by a semantic machine instruction. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

def countValue (source : RequestParser.Stack → List Bool) (m : ℕ) : ℕ × (ℕ × (ℕ × ℕ)) :=
  ParameterCounts.result (ParameterCountsBank.input source m)

def countResult (d : Data) (source : RequestParser.Stack → List Bool) (m : ℕ) : Data :=
  {d with counts := (ParameterCountsBank.resultTapes (ParameterValidation.prepared source 4)
    (encodeNat m) (ParameterCounts.outputEncoding.encode (countValue source m)))}

def extractedData (d : Data) (samples groups : List Bool) : Data where
  counts := Function.update d.counts (ParameterCountsBank.arithmeticMap ParameterCountsBank.Arithmetic.output) []
  formula := d.formula
  mass := d.mass
  budget := TapeBudget.Bank.ready (budgetWords samples groups [] []) []
  scratch := d.scratch
  output := d.output

theorem empty_budget_pair (samples groups : List Bool) :
    Function.update (Function.update (fun _ : TapeBudget.Bank.Stack => [])
      (TapeBudget.Bank.original 0) samples) (TapeBudget.Bank.original 1) groups =
      TapeBudget.Bank.ready (budgetWords samples groups [] []) [] := by
  funext k
  rcases k with k | (k | k)
  · fin_cases k <;> rfl
  · fin_cases k <;> rfl
  · change [] = wordTape TapeBudget.Bank.Engine.input [] k
    simp only [wordTape, Function.update_apply, ite_self]

theorem tuple_data (d : Data) (samples groups : List Bool) (hb : d.budget = fun _ => []) :
    tupleResult d.tapes samples groups = (extractedData d samples groups).tapes := by
  change Function.update (Function.update (Function.update d.tapes
    (countsStacks (ParameterCountsBank.arithmeticMap ParameterCountsBank.Arithmetic.output)) [])
    (budgetStacks (TapeBudget.Bank.original 0)) samples)
    (budgetStacks (TapeBudget.Bank.original 1)) groups = _
  rw [update_counts, update_budget, update_budget]
  dsimp only
  rw [hb, empty_budget_pair]
  rfl

def tupleCost (source : RequestParser.Stack → List Bool) (m : ℕ) : ℕ :=
  let r := countValue source m
  2 * ((encodeNat r.1).length + (encodeNat r.2.1).length +
    (encodeNat r.2.2.1).length + (encodeNat r.2.2.2).length) + 8

theorem extract_count_result (d : Data) (source : RequestParser.Stack → List Bool)
    (m : ℕ) (memory : Memory) (hb : d.budget = fun _ => []) (ht : d.scratch = []) :
    RunsExactly computer.step (configuration (.dropScan 0) (none, memory) (countResult d source m))
      (configuration (.copyMove .mass) (none, memory)
        (extractedData (countResult d source m)
          (encodeNat (countValue source m).2.2.1) (encodeNat (countValue source m).2.2.2)))
      (tupleCost source m) := by
  let r := countValue source m
  have hw : (countResult d source m).tapes countOutput =
      countTuple (encodeNat r.1) (encodeNat r.2.1) (encodeNat r.2.2.1) (encodeNat r.2.2.2) := by
    change wordTape ParameterCountsBank.Arithmetic.output
      (ParameterCounts.outputEncoding.encode r) ParameterCountsBank.Arithmetic.output = _
    rw [wordTape_at]
    exact output_tuple r.1 r.2.1 r.2.2.1 r.2.2.2
  have hs : (countResult d source m).tapes (budgetOriginal 0) = [] := by
    change d.budget (TapeBudget.Bank.original 0) = []; rw [hb]
  have hg : (countResult d source m).tapes (budgetOriginal 1) = [] := by
    change d.budget (TapeBudget.Bank.original 1) = []; rw [hb]
  have run := tuple_run memory (countResult d source m).tapes
    (encodeNat r.1) (encodeNat r.2.1) (encodeNat r.2.2.1) (encodeNat r.2.2.2)
    hw hs hg ht
  have hb' : (countResult d source m).budget = fun _ => [] := hb
  rw [tuple_data (countResult d source m) _ _ hb'] at run
  exact run

end
end Counting.Algorithm.KarpLubyRequest.Preparation
