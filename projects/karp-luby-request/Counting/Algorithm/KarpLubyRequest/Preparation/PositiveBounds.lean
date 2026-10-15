import Counting.Algorithm.KarpLubyRequest.Preparation.StageBounds

/-!
# Polynomial time for the actual positive-mass preparation prefix

The initial parameter words and normalized clause word are charged to the
starting physical bank. Every later space bound follows from a concrete source
run and its executed pushes. Binary sample/group counts are computed here;
their numerical iteration is performed and charged by the later evaluator.
-/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose Polynomial
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

def positiveCopyPolynomial : Polynomial ℕ := 2 * X + 2
def positiveCountSpacePolynomial : Polynomial ℕ :=
  X + (positiveCopyPolynomial + countArithmeticPolynomial) * C primitiveBudget
def positiveTuplePolynomial : Polynomial ℕ := 2 * positiveCountSpacePolynomial + 8
def positiveExtractSpacePolynomial : Polynomial ℕ :=
  positiveCountSpacePolynomial + positiveTuplePolynomial * C primitiveBudget
def positiveBudgetCopyPolynomial : Polynomial ℕ := 4 * positiveExtractSpacePolynomial + 4
def positiveBudgetSpacePolynomial : Polynomial ℕ :=
  positiveExtractSpacePolynomial + positiveBudgetCopyPolynomial * C primitiveBudget

/-- All coefficients are fixed data of the actual source programs. -/
def positivePolynomial : Polynomial ℕ :=
  TapeBudget.Bank.timePolynomial.comp (4 * positiveBudgetSpacePolynomial) +
    positiveBudgetCopyPolynomial + positiveTuplePolynomial +
    countArithmeticPolynomial + positiveCopyPolynomial

theorem positiveCopyPolynomial_eval (n : ℕ) :
    positiveCopyPolynomial.eval n = 2 * n + 2 := by
  simp only [positiveCopyPolynomial, eval_add, eval_mul, eval_ofNat, eval_X]

theorem positiveCountSpacePolynomial_eval (n : ℕ) :
    positiveCountSpacePolynomial.eval n =
      n + (positiveCopyPolynomial.eval n + countArithmeticPolynomial.eval n) * primitiveBudget := by
  simp only [positiveCountSpacePolynomial, eval_add, eval_mul, eval_C, eval_X]

theorem positiveTuplePolynomial_eval (n : ℕ) :
    positiveTuplePolynomial.eval n = 2 * positiveCountSpacePolynomial.eval n + 8 := by
  simp only [positiveTuplePolynomial, eval_add, eval_mul, eval_ofNat]

theorem positiveExtractSpacePolynomial_eval (n : ℕ) :
    positiveExtractSpacePolynomial.eval n =
      positiveCountSpacePolynomial.eval n + positiveTuplePolynomial.eval n * primitiveBudget := by
  simp only [positiveExtractSpacePolynomial, eval_add, eval_mul, eval_C]

theorem positiveBudgetCopyPolynomial_eval (n : ℕ) :
    positiveBudgetCopyPolynomial.eval n = 4 * positiveExtractSpacePolynomial.eval n + 4 := by
  simp only [positiveBudgetCopyPolynomial, eval_add, eval_mul, eval_ofNat]

theorem positiveBudgetSpacePolynomial_eval (n : ℕ) :
    positiveBudgetSpacePolynomial.eval n =
      positiveExtractSpacePolynomial.eval n + positiveBudgetCopyPolynomial.eval n * primitiveBudget := by
  simp only [positiveBudgetSpacePolynomial, eval_add, eval_mul, eval_C]

theorem positivePolynomial_eval (n : ℕ) :
    positivePolynomial.eval n =
      TapeBudget.Bank.timeBound (4 * positiveBudgetSpacePolynomial.eval n) +
        positiveBudgetCopyPolynomial.eval n + positiveTuplePolynomial.eval n +
        countArithmeticPolynomial.eval n + positiveCopyPolynomial.eval n := by
  simp only [positivePolynomial, eval_add, eval_comp, eval_mul, eval_ofNat,
    TapeBudget.Bank.timePolynomial_eval]

set_option maxHeartbeats 800000 in
/-- The bound concerns this exact five-stage source prefix, on its actual
retained bank. It does not require validity, a numeric count bound, or an
assumed evaluator for any arithmetic operation. -/
theorem positive_time_le (source : RequestParser.Stack → List Bool) (f : Formula source) :
    positivePrefixTime source f ≤ positivePolynomial.eval (stackSize (normalizedData source f).tapes) := by
  let d := normalizedData source f
  let S := stackSize d.tapes
  let m := clauseCount source f
  let x := gateInput source f
  let countTime := 1 + ((ParameterCounts.computes.outputs (ParameterCountsBank.input source m)).steps +
    ParameterCountsBank.serializeTime (ParameterValidation.prepared source 4) (encodeNat m))
  let copyTime := 2 * (encodeNat m).length + 2
  let budgetCopyTime := 2 * ((encodeNat x.2.2.1).length + (randomWord source).length) + 4

  have hfields : ∀ i, (ParameterValidation.rawField source i).length ≤ S := by
    intro i
    have h := word_length_le d.tapes (parameterStacks (ParameterProgram.field i))
    exact h
  have hm : (encodeNat m).length ≤ S := by
    exact word_length_le d.tapes (formulaStacks 4)
  have hcopy : copyTime ≤ positiveCopyPolynomial.eval S := by
    rw [positiveCopyPolynomial_eval]
    dsimp only [copyTime]
    omega
  have hcount : countTime ≤ countArithmeticPolynomial.eval S :=
    count_arithmetic_le source m S hfields hm

  have copyRun := count_input_copy source d (workingMemory false) m rfl rfl rfl
  have countRun := counts_call d (workingMemory false) source m
  have countSpace := stored_bits _ _ _ (copyRun.trans countRun)
  change stackSize (countResult d source m).tapes ≤ S + (countTime + copyTime) * primitiveBudget at countSpace
  have hcountSpace : stackSize (countResult d source m).tapes ≤ positiveCountSpacePolynomial.eval S := by
    apply countSpace.trans
    rw [positiveCountSpacePolynomial_eval]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right primitiveBudget (by omega)) S

  have htuple : tupleCost source m ≤ positiveTuplePolynomial.eval S := by
    have h := tuple_cost_le_stack d source m
    rw [positiveTuplePolynomial_eval]
    omega
  have tupleRun := extract_count_result d source m (workingMemory false) rfl rfl
  have tupleSpace := stored_bits _ _ _ tupleRun
  change stackSize (extractedCounts source f).tapes ≤
    stackSize (countResult d source m).tapes + tupleCost source m * primitiveBudget at tupleSpace
  have hextractedSpace : stackSize (extractedCounts source f).tapes ≤ positiveExtractSpacePolynomial.eval S := by
    apply tupleSpace.trans
    rw [positiveExtractSpacePolynomial_eval]
    exact Nat.add_le_add hcountSpace (Nat.mul_le_mul_right primitiveBudget htuple)

  have hmass : (encodeNat x.2.2.1).length ≤ stackSize (extractedCounts source f).tapes := by
    exact word_length_le (extractedCounts source f).tapes (massStacks 2)
  have htape : (randomWord source).length ≤ stackSize (extractedCounts source f).tapes := by
    exact word_length_le (extractedCounts source f).tapes tapeSource
  have hbudgetCopy : budgetCopyTime ≤ positiveBudgetCopyPolynomial.eval S := by
    rw [positiveBudgetCopyPolynomial_eval]
    dsimp only [budgetCopyTime]
    omega

  have budgetCopyRun := budget_input_copy (extractedCounts source f) (workingMemory false)
    (encodeNat x.1) (encodeNat x.2.1) (encodeNat x.2.2.1) (randomWord source) rfl rfl rfl rfl
  have budgetSpace := stored_bits _ _ _ budgetCopyRun
  change stackSize (gatedData source f).tapes ≤
    stackSize (extractedCounts source f).tapes + budgetCopyTime * primitiveBudget at budgetSpace
  have hbudgetSpace : stackSize (gatedData source f).tapes ≤ positiveBudgetSpacePolynomial.eval S := by
    apply budgetSpace.trans
    rw [positiveBudgetSpacePolynomial_eval]
    exact Nat.add_le_add hextractedSpace (Nat.mul_le_mul_right primitiveBudget hbudgetCopy)
  have hphysical := budget_physical_le_stack (gatedData source f) x rfl
  have hbudget : TapeBudget.Bank.steps x ≤
      TapeBudget.Bank.timeBound (4 * positiveBudgetSpacePolynomial.eval S) := by
    exact (TapeBudget.Bank.steps_le x).trans (budget_time_mono (by omega))

  change TapeBudget.Bank.steps x + budgetCopyTime + tupleCost source m + countTime + copyTime ≤ _
  rw [positivePolynomial_eval]
  change TapeBudget.Bank.steps x + budgetCopyTime + tupleCost source m + countTime + copyTime ≤
    TapeBudget.Bank.timeBound (4 * positiveBudgetSpacePolynomial.eval S) +
      positiveBudgetCopyPolynomial.eval S + positiveTuplePolynomial.eval S +
      countArithmeticPolynomial.eval S + positiveCopyPolynomial.eval S
  omega

end
end Counting.Algorithm.KarpLubyRequest.Preparation
