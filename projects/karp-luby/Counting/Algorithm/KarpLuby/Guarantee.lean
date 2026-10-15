import Counting.Algorithm.KarpLuby.ProgramCorrectness
import Counting.Algorithm.KarpLuby.TapeProduct
import Counting.Algorithm.KarpLuby.ProgramEncoding

/-!
# PAC correctness of the executable general-DNF program

The theorem is about `Program.run` on its actual finite Boolean tape domain,
including rational accuracy/confidence adapters and exact zero. No hypothetical
single-trial moments or sampler correctness hypotheses remain. Machine bit-time
is a separate obligation and is not asserted by this module.
-/
namespace Counting.Algorithm.KarpLuby.Program

open DNF HiddenCircuits.Approximation.SelfReduction
variable {n : ℕ}

/-- Zero target count is exact for every finite tape and every sample budget. -/
theorem estimate_zero (cs : List (Clause n)) (s g : ℕ)
    (hc : count (clauseFamily cs) = 0)
    (tape : CoinTape (randomBitBudget cs s g)) : estimate cs s g tape = 0 := by
  apply median_all_zero
  intro i
  simp [groupAverage, naturalAverage, trial_of_count_zero cs hc]

@[simp] theorem count_normalizedClauseFamily (f : Formula n) :
    count (clauseFamily (normalizeFormula f)) = modelCount f := count_normalizedCover f

/-- The complete DNF adapter preserves exact zero without any accuracy promise. -/
theorem run_zero (f : Formula n) (epsilon delta : ℚ) (hc : modelCount f = 0)
    (tape : CoinTape (requestedBudget f epsilon delta)) : run f epsilon delta tape = 0 := by
  exact estimate_zero (normalizeFormula f) _ _ (by simpa using hc) tape

/-- End-to-end relative PAC guarantee for the concrete fixed-tape DNF program. -/
theorem run_failure (f : Formula n) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    probability (fun tape : CoinTape (requestedBudget f epsilon delta) =>
      epsilon * (modelCount f : ℚ) < |run f epsilon delta tape - modelCount f|) ≤ delta := by
  by_cases hc : modelCount f = 0
  · have hz := run_zero f epsilon delta hc
    simp [probability, hz, hc, mean, hd.le]
  · have hC : (0 : ℚ) < modelCount f := by exact_mod_cast Nat.pos_of_ne_zero hc
    have hm : 0 < (normalizeFormula f).length := by
      apply List.length_pos_iff.mpr
      intro hnil
      exact hc ((modelCount_eq_zero_iff_normalizeFormula f).mpr hnil)
    have hmean := mean_trial (normalizeFormula f)
    have hsecond := secondMoment_trial_le (normalizeFormula f)
    simp only [count_normalizedClauseFamily] at hmean hsecond
    have hf := estimate_failure_of_moments (normalizeFormula f) (modelCount f)
      (normalizeFormula f).length (samples (normalizeFormula f).length epsilon)
      (confidenceGroups delta) epsilon hmean hsecond hC (samples_pos hm epsilon) he
      (samples_accuracy_budget (normalizeFormula f).length he)
    exact hf.trans (confidenceGroups_failure_le hd)

/-- The requested relative-error interval holds with probability at least 1−δ. -/
theorem run_success (f : Formula n) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    1 - delta ≤ probability (fun tape : CoinTape (requestedBudget f epsilon delta) =>
      |run f epsilon delta tape - modelCount f| ≤ epsilon * modelCount f) := by
  have hf := run_failure f epsilon delta he hd
  have hc := probability_compl (fun tape : CoinTape (requestedBudget f epsilon delta) =>
    epsilon * (modelCount f : ℚ) < |run f epsilon delta tape - modelCount f|)
  simp only [not_lt] at hc
  linarith

/-- Multiplicative interval version, for all explicit formulas and positive requests. -/
theorem run_multiplicative (f : Formula n) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    1 - delta ≤ probability (fun tape : CoinTape (requestedBudget f epsilon delta) =>
      (1 - epsilon) * (modelCount f : ℚ) ≤ run f epsilon delta tape ∧
      run f epsilon delta tape ≤ (1 + epsilon) * (modelCount f : ℚ)) := by
  apply (run_success f epsilon delta he hd).trans
  apply probability_mono
  intro tape ht
  obtain ⟨hl, hu⟩ := abs_le.mp ht
  constructor <;> nlinarith

/-- Binary output is decoded to the exact rational analyzed by `run_success`. -/
theorem runEncoded_correct (f : Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (requestedBudget f epsilon delta)) :
    Encoding.decodeOutput (runEncoded f epsilon delta tape) = some (run f epsilon delta tape) :=
  Encoding.decode_encodeOutput _

/-- PAC correctness survives the actual request parser and binary output codec. -/
theorem evalBits_success (f : Formula n) (epsilon delta : ℚ)
    (hvalid : ValidRequest epsilon delta) :
    1 - delta ≤ probability (fun tape : CoinTape (requestedBudget f epsilon delta) =>
      ∃ z : ℚ, Encoding.decodeOutput
        (ProgramEncoding.evalBits (ProgramEncoding.encodeRun f epsilon delta tape)) = some z ∧
        |z - modelCount f| ≤ epsilon * modelCount f) := by
  apply (run_success f epsilon delta hvalid.1 hvalid.2.2.1).trans
  apply probability_mono
  intro tape hgood
  exact ⟨run f epsilon delta tape,
    ProgramEncoding.decode_evalBits_encodeRun f epsilon delta hvalid tape, hgood⟩

end Counting.Algorithm.KarpLuby.Program
