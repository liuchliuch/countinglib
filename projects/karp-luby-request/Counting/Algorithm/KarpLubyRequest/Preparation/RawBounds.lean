import Counting.Algorithm.KarpLubyRequest.Preparation.RawRun
import Counting.Algorithm.KarpLubyRequest.Preparation.PositiveBounds

/-! A fixed polynomial for the complete actual raw preparation machine.
Every later input-word size is obtained from an actual earlier run's stored-bit
bound. In particular, retaining malformed fields and clearing a failure bank
are charged, and no decoded binary parameter is treated as a free loop bound. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

private theorem max_le_sum_of_bounds {a b x y : ℕ} (ha : a ≤ x) (hb : b ≤ y) :
    max a b ≤ x + y := by omega

noncomputable def normalizationPolynomial : Polynomial ℕ :=
  20 * (Polynomial.X * (4 * Polynomial.X + 1) + 1) ^ 2 +
    2 * (Polynomial.X * (4 * Polynomial.X + 1)) +
    23 * Polynomial.X ^ 2 + 80 * Polynomial.X + 19

theorem normalizationPolynomial_eval (n : ℕ) :
    normalizationPolynomial.eval n = normalizationPolynomialBound n := by
  simp only [normalizationPolynomial, normalizationPolynomialBound, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one,
    Polynomial.eval_X]

noncomputable def serializationPolynomial : Polynomial ℕ :=
  (2 * Polynomial.X + 2) +
    8 * (Polynomial.X + (2 * Polynomial.X + 2) * Polynomial.C primitiveBudget) + 12
noncomputable def finishPolynomial : Polynomial ℕ :=
  serializationPolynomial + (Polynomial.X + serializationPolynomial * Polynomial.C primitiveBudget) +
    Polynomial.C workCount + 3

theorem finishPolynomial_eval (n : ℕ) : finishPolynomial.eval n = finishBound n := by
  simp only [finishPolynomial, serializationPolynomial, finishBound, serializationBound,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
    Polynomial.eval_C]

noncomputable def normalizedSpacePolynomial : Polynomial ℕ :=
  Polynomial.X + normalizationPolynomial * Polynomial.C primitiveBudget
noncomputable def positiveTimePolynomial : Polynomial ℕ :=
  positivePolynomial.comp normalizedSpacePolynomial
noncomputable def gateSpacePolynomial : Polynomial ℕ :=
  normalizedSpacePolynomial + positiveTimePolynomial * Polynomial.C primitiveBudget
noncomputable def acceptedPolynomial : Polynomial ℕ :=
  normalizationPolynomial + 1 +
    (positiveTimePolynomial + 1 +
      (finishPolynomial.comp gateSpacePolynomial + gateSpacePolynomial + Polynomial.C (workCount + 3))) +
    (normalizedSpacePolynomial + Polynomial.C (workCount + 3))

theorem normalization_cost_physical (source : RequestParser.Stack → List Bool) (f : Formula source)
    (hf : (Encoding.formula (variableWord source).length).decode (formulaWord source) = some f) :
    normalizationCost source f ≤ normalizationPolynomial.eval (stackSize (validatedData source).tapes) := by
  rw [normalizationPolynomial_eval]
  apply normalization_cost_le source f hf
  · simpa only [variableWord_stored] using word_length_le (validatedData source).tapes variableSource
  · simpa only [formulaWord_stored] using word_length_le (validatedData source).tapes formulaSource

theorem normalized_space_le (source : RequestParser.Stack → List Bool) (f : Formula source)
    (hf : (Encoding.formula (variableWord source).length).decode (formulaWord source) = some f) :
    stackSize (normalizedData source f).tapes ≤
      normalizedSpacePolynomial.eval (stackSize (validatedData source).tapes) := by
  obtain ⟨bit, time, bound, run⟩ := normalize_mass source f hf
  have hs := stored_bits _ _ time run
  have ht := normalization_cost_physical source f hf
  have hm := Nat.mul_le_mul_right primitiveBudget (bound.trans ht)
  change stackSize (normalizedData source f).tapes ≤
    stackSize (validatedData source).tapes + time * primitiveBudget at hs
  simp only [normalizedSpacePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C]
  exact hs.trans (Nat.add_le_add_left hm _)

theorem positive_time_physical (source : RequestParser.Stack → List Bool) (f : Formula source)
    (hf : (Encoding.formula (variableWord source).length).decode (formulaWord source) = some f) :
    positivePrefixTime source f ≤ positiveTimePolynomial.eval (stackSize (validatedData source).tapes) := by
  have h := positive_time_le source f
  have hm := natPolynomial_eval_mono positivePolynomial (normalized_space_le source f hf)
  rw [positiveTimePolynomial, Polynomial.eval_comp]
  exact h.trans hm

theorem gated_space_le (source : RequestParser.Stack → List Bool) (f : Formula source)
    (hf : (Encoding.formula (variableWord source).length).decode (formulaWord source) = some f) :
    stackSize (gatedData source f).tapes ≤
      gateSpacePolynomial.eval (stackSize (validatedData source).tapes) := by
  have h := stored_bits _ _ _ (positive_prefix source f false)
  change stackSize (gatedData source f).tapes ≤
    stackSize (normalizedData source f).tapes + positivePrefixTime source f * primitiveBudget at h
  have hn := normalized_space_le source f hf
  have ht := positive_time_physical source f hf
  have hm := Nat.mul_le_mul_right primitiveBudget ht
  simp only [gateSpacePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  exact h.trans (Nat.add_le_add hn hm)

set_option maxRecDepth 4096 in
/-- The accepted continuation's complete stage cost, including the mass-zero
shortcut and the dirty-bank cleanup, is bounded by one fixed polynomial. -/
theorem accepted_cost_le (source : RequestParser.Stack → List Bool) (f : Formula source)
    (hf : (Encoding.formula (variableWord source).length).decode (formulaWord source) = some f) :
    acceptedCost source f ≤ acceptedPolynomial.eval (stackSize (validatedData source).tapes) := by
  let n := stackSize (validatedData source).tapes
  have hn := normalization_cost_physical source f hf
  have hns := normalized_space_le source f hf
  have ht := positive_time_physical source f hf
  have hgs := gated_space_le source f hf
  have hfinish : finishBound (stackSize (gatedData source f).tapes) ≤
      finishPolynomial.eval (gateSpacePolynomial.eval n) := by
    rw [finishPolynomial_eval]
    exact finishBound_mono hgs
  have hmax1 : max (finishBound (stackSize (gatedData source f).tapes))
      (stackSize (gatedData source f).tapes + workCount + 3) ≤
      finishPolynomial.eval (gateSpacePolynomial.eval n) + gateSpacePolynomial.eval n + (workCount + 3) := by
    simpa only [Nat.add_assoc] using max_le_sum_of_bounds hfinish
      (Nat.add_le_add_right (Nat.add_le_add_right hgs workCount) 3)
  have hmax2 : max
      (positivePrefixTime source f + 1 + max (finishBound (stackSize (gatedData source f).tapes))
        (stackSize (gatedData source f).tapes + workCount + 3))
      (stackSize (normalizedData source f).tapes + workCount + 3) ≤
      positiveTimePolynomial.eval n + 1 +
        (finishPolynomial.eval (gateSpacePolynomial.eval n) + gateSpacePolynomial.eval n + (workCount + 3)) +
        (normalizedSpacePolynomial.eval n + (workCount + 3)) := by
    simpa only [Nat.add_assoc] using max_le_sum_of_bounds
      (Nat.add_le_add (Nat.add_le_add_right ht 1) hmax1)
      (Nat.add_le_add_right (Nat.add_le_add_right hns workCount) 3)
  dsimp only [acceptedCost]
  simp only [acceptedPolynomial, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_comp, Polynomial.eval_C]
  have bound := Nat.add_le_add (Nat.add_le_add_right hn 1) hmax2
  simpa only [Nat.add_assoc] using bound

noncomputable def parserPolynomial : Polynomial ℕ :=
  2 * Polynomial.X ^ 4 + 18 * Polynomial.X ^ 3 + 39 * Polynomial.X ^ 2 + 84 * Polynomial.X + 150

theorem parserPolynomial_eval (n : ℕ) : parserPolynomial.eval n = ParameterValidation.timeBound n := by
  dsimp only [ParameterValidation.timeBound]
  rw [RequestParser.timeBound_eq]
  simp only [parserPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

noncomputable def parserSpacePolynomial : Polynomial ℕ :=
  Polynomial.X + parserPolynomial * Polynomial.C primitiveBudget
noncomputable def rejectedPolynomial : Polynomial ℕ :=
  parserPolynomial + 1 +
    (Polynomial.X + (parserPolynomial + 1) * Polynomial.C primitiveBudget) + Polynomial.C workCount + 3

theorem rejectedPolynomial_eval (n : ℕ) : rejectedPolynomial.eval n = rejectedBound n := by
  simp only [rejectedPolynomial, rejectedBound, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_X,
    parserPolynomial_eval]

noncomputable def rawPolynomial : Polynomial ℕ :=
  parserPolynomial + acceptedPolynomial.comp parserSpacePolynomial + rejectedPolynomial
noncomputable def rawBound (n : ℕ) : ℕ := rawPolynomial.eval n

/-- Full physical polynomial bound for the exact all-raw run, including every
source call, each retained copy, all discarded fields, the gate, and cleanup. -/
theorem raw_run_bounded (raw : List Bool) :
    ∃ time, time ≤ rawBound raw.length ∧
      RunsExactly computer.step (initList computer raw) (haltList computer (rawResult raw)) time := by
  rw [halt_eq]
  cases hs : parameterStatus raw with
  | false =>
    obtain ⟨time, bound, run⟩ := rejected_run raw hs
    refine ⟨time, ?_, ?_⟩
    · dsimp only [rawBound]
      simp only [rawPolynomial, Polynomial.eval_add]
      rw [rejectedPolynomial_eval]
      exact bound.trans (Nat.le_add_left _ _)
    · rw [rawResult_rejected raw hs]
      exact run
  | true =>
    obtain ⟨r, hd, hv⟩ := status_true_decode raw hs
    obtain ⟨ending, parserTime, parserBound, parserRun, keep⟩ := parameter_call raw
    obtain ⟨source, fields, hfields, hsep, he⟩ := keep r hd hv
    obtain ⟨f, hf, hp, ht⟩ := RawSemantics.decoded_source hfields hsep hd
    rw [hs, he] at parserRun
    obtain ⟨time, bound, run⟩ := accepted_run source f hf
    have hout := preparedResult_original hfields hsep hd hv f hp ht
    rw [hout] at run
    have hsize := stored_bits_from_raw raw _ parserTime parserRun
    change stackSize (validatedData source).tapes ≤ raw.length + parserTime * primitiveBudget at hsize
    have hmul := Nat.mul_le_mul_right primitiveBudget parserBound
    have hsized : stackSize (validatedData source).tapes ≤ parserSpacePolynomial.eval raw.length := by
      simp only [parserSpacePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_C, parserPolynomial_eval]
      exact hsize.trans (Nat.add_le_add_left hmul _)
    have ha := accepted_cost_le source f hf
    have hb := natPolynomial_eval_mono acceptedPolynomial hsized
    refine ⟨time + parserTime, ?_, ?_⟩
    · dsimp only [rawBound]
      simp only [rawPolynomial, Polynomial.eval_add, Polynomial.eval_comp, parserPolynomial_eval]
      rw [Nat.add_comm time parserTime]
      exact (Nat.add_le_add parserBound (bound.trans (ha.trans hb))).trans (Nat.le_add_right _ _)
    · have hall := parserRun.trans run
      simpa only [rawResult, hd, Option.elim_some, requestResult, hv, ite_true] using hall

end
end Counting.Algorithm.KarpLubyRequest.Preparation
