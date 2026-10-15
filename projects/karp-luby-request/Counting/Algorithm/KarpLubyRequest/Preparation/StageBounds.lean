import Counting.Algorithm.KarpLubyRequest.Preparation.PositiveRun

/-! Bounds for the actual arithmetic stages in physical stack words. Numeric
sample/group values are outputs here; their later iteration is charged by the
sampling machine separately. All polynomial coefficients are fixed source data. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

def countArithmeticPolynomial : Polynomial ℕ :=
  18 * Polynomial.X + 39 + ParameterCounts.computes.time.comp (9 * Polynomial.X + 12)

def countArithmeticBound (n : ℕ) : ℕ := countArithmeticPolynomial.eval n

theorem countArithmeticBound_eq (n : ℕ) :
    countArithmeticBound n = 18 * n + 39 + ParameterCounts.computes.time.eval (9 * n + 12) := by
  simp only [countArithmeticBound, countArithmeticPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_comp]

theorem count_arithmetic_le (source : RequestParser.Stack → List Bool) (m n : ℕ)
    (hf : ∀ i, (ParameterValidation.rawField source i).length ≤ n)
    (hm : (encodeNat m).length ≤ n) :
    1 + ((ParameterCounts.computes.outputs (ParameterCountsBank.input source m)).steps +
      ParameterCountsBank.serializeTime (ParameterValidation.prepared source 4) (encodeNat m)) ≤
      countArithmeticBound n := by
  have ht := ParameterCountsBank.time_le source m n hf
  have hp := natPolynomial_eval_mono ParameterCounts.computes.time
    (show 8 * n + (encodeNat m).length + 12 ≤ 9 * n + 12 by omega)
  dsimp only [ParameterCountsBank.timeBound] at ht
  rw [countArithmeticBound_eq]
  omega

theorem tuple_cost_le_word (source : RequestParser.Stack → List Bool) (m : ℕ) :
    tupleCost source m ≤
      2 * (ParameterCounts.outputEncoding.encode (countValue source m)).length + 8 := by
  let r := countValue source m
  have he := output_tuple r.1 r.2.1 r.2.2.1 r.2.2.2
  change ParameterCounts.outputEncoding.encode r = _ at he
  change 2 * ((encodeNat r.1).length + (encodeNat r.2.1).length +
    (encodeNat r.2.2.1).length + (encodeNat r.2.2.2).length) + 8 ≤ _
  rw [he]
  simp only [countTuple, List.length_append, Encoding.frame_length]
  omega

theorem tuple_cost_le_stack (d : Data) (source : RequestParser.Stack → List Bool) (m : ℕ) :
    tupleCost source m ≤ 2 * stackSize (countResult d source m).tapes + 8 := by
  have h := word_length_le (countResult d source m).tapes countOutput
  have he : (countResult d source m).tapes countOutput =
      ParameterCounts.outputEncoding.encode (countValue source m) := by
    change wordTape ParameterCountsBank.Arithmetic.output
      (ParameterCounts.outputEncoding.encode (countValue source m)) ParameterCountsBank.Arithmetic.output = _
    exact wordTape_at _ _
  rw [he] at h
  have ht := tuple_cost_le_word source m
  omega

theorem budget_physical_le_stack (d : Data) (x : TapeBudget.Arithmetic.Input)
    (hd : d.budget = TapeBudget.Bank.ready (TapeBudget.Bank.prepared x) []) :
    TapeBudget.Bank.physicalSize x ≤ 4 * stackSize d.tapes := by
  have a := word_length_le d.tapes (budgetOriginal 0)
  have b := word_length_le d.tapes (budgetOriginal 1)
  have c := word_length_le d.tapes (budgetOriginal 2)
  have e := word_length_le d.tapes (budgetOriginal 3)
  change (d.budget (TapeBudget.Bank.original 0)).length ≤ _ at a
  change (d.budget (TapeBudget.Bank.original 1)).length ≤ _ at b
  change (d.budget (TapeBudget.Bank.original 2)).length ≤ _ at c
  change (d.budget (TapeBudget.Bank.original 3)).length ≤ _ at e
  rw [hd] at a b c e
  change (encodeNat x.1).length ≤ _ at a
  change (encodeNat x.2.1).length ≤ _ at b
  change (encodeNat x.2.2.1).length ≤ _ at c
  change x.2.2.2.length ≤ _ at e
  dsimp only [TapeBudget.Bank.physicalSize]
  omega

theorem budget_time_mono {a b : ℕ} (h : a ≤ b) :
    TapeBudget.Bank.timeBound a ≤ TapeBudget.Bank.timeBound b := by
  rw [← TapeBudget.Bank.timePolynomial_eval, ← TapeBudget.Bank.timePolynomial_eval]
  exact natPolynomial_eval_mono _ h

theorem serializationBound_mono {a b : ℕ} (h : a ≤ b) : serializationBound a ≤ serializationBound b := by
  dsimp only [serializationBound]
  gcongr

theorem finishBound_mono {a b : ℕ} (h : a ≤ b) : finishBound a ≤ finishBound b := by
  have hh := serializationBound_mono h
  dsimp only [finishBound]
  gcongr

end
end Counting.Algorithm.KarpLubyRequest.Preparation
