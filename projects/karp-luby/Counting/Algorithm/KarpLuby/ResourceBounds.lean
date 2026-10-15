import Counting.Algorithm.KarpLuby.Cost

/-!
# Bounds for the production tape and rational output

These theorems apply to the actual program definitions. Clause count is measured
before normalization, and the explicit ambient variable count is retained.
They bound random-bit allocation and binary output magnitudes, separately from
the still-distinct machine transition-cost obligation.
-/

namespace Counting.Algorithm.KarpLuby.ResourceBounds

open DNF

variable {n : ℕ}

 theorem normalized_length_le (f : Formula n) : (normalizeFormula f).length ≤ f.length :=
  List.length_filterMap_le _ _

 theorem totalMass_le (cs : List (Clause n)) :
    Program.totalMass cs ≤ cs.length * 2 ^ n := by
  have h := Cost.sum_le_length_mul_pow n (cs.map clauseMass) (by
    intro a ha
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp ha
    exact clauseMass_le c)
  simpa [Program.totalMass] using h

 theorem normalized_totalMass_le (f : Formula n) :
    Program.totalMass (normalizeFormula f) ≤ f.length * 2 ^ n :=
  (totalMass_le _).trans (Nat.mul_le_mul_right _ (normalized_length_le f))

 theorem normalized_dyadicBits_le (f : Formula n) :
    dyadicBits (Program.totalMass (normalizeFormula f)) ≤ f.length.size + n + 1 := by
  exact (Cost.totalMass_size_le _).trans
    (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.size_le_size (normalized_length_le f)) n) 1)

/-- Exact allocated tape length bounded using the original number of input terms. -/
theorem requestedBudget_le_raw (f : Formula n) (epsilon delta : ℚ) :
    Program.requestedBudget f epsilon delta ≤
      2 * (delta.den.size + 2) *
        (144 * f.length * reciprocalCeiling epsilon ^ 2 * (f.length.size + n + 1)) := by
  refine (Cost.requestedBudget_le f epsilon delta).trans ?_
  have hm := normalized_length_le f
  have hs := Nat.size_le_size hm
  gcongr

/-- Polynomial dependence on inverse relative error and confidence encoding length. -/
theorem requestedBudget_le_inverse_polynomial (f : Formula n) {epsilon : ℚ}
    (he : 0 < epsilon) (delta : ℚ) :
    (Program.requestedBudget f epsilon delta : ℚ) ≤
      2 * (delta.den.size + 2 : ℚ) *
        (144 * (f.length : ℚ) * (1 / epsilon + 1) ^ 2 *
          (f.length.size + n + 1 : ℚ)) := by
  have h : (Program.requestedBudget f epsilon delta : ℚ) ≤
      2 * (delta.den.size + 2 : ℚ) *
        (144 * (f.length : ℚ) * (reciprocalCeiling epsilon : ℚ) ^ 2 *
          (f.length.size + n + 1 : ℚ)) := by
    exact_mod_cast requestedBudget_le_raw f epsilon delta
  refine h.trans ?_
  have hc := reciprocalCeiling_le_inv_add_one he
  gcongr

/-- The production median selects an actual group numerator over the common
sample denominator, so denominator multiplication across groups is unnecessary. -/
theorem estimate_has_fraction (cs : List (Clause n)) (N G : ℕ)
    (tape : CoinTape (Program.randomBitBudget cs N G)) (hG : 0 < G) :
    ∃ a : ℕ, a ≤ N * dyadicSize (Program.totalMass cs) ∧
      a.size ≤ N.size + cs.length.size + n + 2 ∧
      Program.estimate cs N G tape = (a : ℚ) / N := by
  obtain ⟨g, hg⟩ := median_eq_observation G
    (fun g => Program.groupAverage cs N (Program.coinChunk tape g)) hG
  let words : Fin N → ℕ := fun s => decodeNat (dyadicBits (Program.totalMass cs))
    (Program.coinChunk (Program.coinChunk tape g) s)
  refine ⟨(List.ofFn fun s => Program.trial cs (words s)).sum, ?_, ?_, hg⟩
  · have h := Cost.sum_le_length_mul
      (List.ofFn fun s => Program.trial cs (words s))
      (dyadicSize (Program.totalMass cs)) (by
        intro x hx
        obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hx
        exact Program.trial_le_scale cs (words s))
    simpa using h
  · exact Cost.sample_numerator_size_le cs N words

/-- Canonical reduction cannot enlarge the absolute numerator of a natural fraction. -/
theorem fraction_num_natAbs_le (a N : ℕ) : ((a : ℚ) / N).num.natAbs ≤ a := by
  by_cases hN : N = 0
  · simp [hN]
  by_cases ha : a = 0
  · simp [ha]
  have hd : (N : ℤ) ≠ 0 := by exact_mod_cast hN
  have han : (a : ℤ) ≠ 0 := by exact_mod_cast ha
  have h := Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd (a : ℤ) hd) han
  simpa [Rat.divInt_eq_div] using h

/-- For a nonzero sample count, canonical denominator reduction only decreases it. -/
theorem fraction_den_le (a N : ℕ) (hN : 0 < N) : ((a : ℚ) / N).den ≤ N := by
  have hd := Rat.den_dvd (a : ℤ) (N : ℤ)
  have hdiv : ((a : ℚ) / N).den ∣ N := by
    exact_mod_cast (show ((((a : ℚ) / N).den : ℕ) : ℤ) ∣ (N : ℤ) by
      simpa [Rat.divInt_eq_div] using hd)
  exact Nat.le_of_dvd hN hdiv

 theorem fraction_den_size_le (a N : ℕ) : ((a : ℚ) / N).den.size ≤ N.size + 1 := by
  by_cases hN : N = 0
  · simp [hN]
  have h := Nat.size_le_size (fraction_den_le a N (Nat.pos_of_ne_zero hN))
  omega

/-- Binary magnitude bounds for the actual canonical rational output encoding.
The bounds also cover zero samples and zero groups. -/
theorem estimate_output_size_le (cs : List (Clause n)) (N G : ℕ)
    (tape : CoinTape (Program.randomBitBudget cs N G)) :
    (Program.encodeOutput (Program.estimate cs N G tape)).1.natAbs.size ≤
        N.size + cs.length.size + n + 2 ∧
    (Program.encodeOutput (Program.estimate cs N G tape)).2.size ≤ N.size + 1 := by
  by_cases hG : 0 < G
  · obtain ⟨a, _, ha, he⟩ := estimate_has_fraction cs N G tape hG
    simp only [Program.encodeOutput, he]
    exact ⟨(Nat.size_le_size (fraction_num_natAbs_le a N)).trans ha,
      fraction_den_size_le a N⟩
  · have hg : G = 0 := by omega
    subst G
    simp [Program.estimate, Program.encodeOutput, median_zero]

/-- Every output is in the closed interval from zero to the dyadic scale. -/
theorem estimate_range (cs : List (Clause n)) (N G : ℕ)
    (tape : CoinTape (Program.randomBitBudget cs N G)) :
    0 ≤ Program.estimate cs N G tape ∧
      Program.estimate cs N G tape ≤ (dyadicSize (Program.totalMass cs) : ℚ) := by
  by_cases hG : 0 < G
  · obtain ⟨a, ha, _, he⟩ := estimate_has_fraction cs N G tape hG
    rw [he]
    constructor
    · positivity
    · by_cases hN : N = 0
      · simp [hN]
      · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hN)).mpr
        exact_mod_cast (by simpa [Nat.mul_comm] using ha)
  · have hg : G = 0 := by omega
    subst G
    simp [Program.estimate, median_zero]


/-- The binary length of the sample count is bounded by the original rational
parameter encoding, including requests handled by the total adapter. -/
theorem samples_size_le (m : ℕ) (epsilon : ℚ) :
    (samples m epsilon).size ≤ m.size + 2 * epsilon.den.size + 10 := by
  have hceil := confidenceGroups_le_den_size epsilon
  unfold confidenceGroups at hceil
  have hm := Cost.size_mul_le 144 m
  have hs := Cost.size_mul_le (reciprocalCeiling epsilon) (reciprocalCeiling epsilon)
  have htotal := Cost.size_mul_le (144 * m)
    (reciprocalCeiling epsilon * reciprocalCeiling epsilon)
  have h144 : (144 : ℕ).size = 8 := rfl
  unfold samples
  rw [pow_two]
  omega

/-- End-to-end binary output bounds for the raw DNF and rational-parameter entry
point. These cover empty formulas, contradictory terms, and zero sample counts. -/
theorem run_output_size_le (f : Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    (Program.encodeOutput (Program.run f epsilon delta tape)).1.natAbs.size ≤
        2 * f.length.size + 2 * epsilon.den.size + n + 12 ∧
    (Program.encodeOutput (Program.run f epsilon delta tape)).2.size ≤
        f.length.size + 2 * epsilon.den.size + 11 := by
  have h := estimate_output_size_le (normalizeFormula f)
    (Program.requestedSamples (normalizeFormula f) epsilon)
    (Program.requestedGroups delta) tape
  have hs := samples_size_le (normalizeFormula f).length epsilon
  have hm := Nat.size_le_size (normalized_length_le f)
  change
    (Program.encodeOutput (Program.run f epsilon delta tape)).1.natAbs.size ≤
        (samples (normalizeFormula f).length epsilon).size +
          (normalizeFormula f).length.size + n + 2 ∧
    (Program.encodeOutput (Program.run f epsilon delta tape)).2.size ≤
        (samples (normalizeFormula f).length epsilon).size + 1 at h
  constructor <;> omega

/-- Length of the actual framed Boolean output returned by `runEncoded`,
including sign, numerator framing, and denominator representation. -/
theorem runEncoded_length_le (f : Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    (Program.runEncoded f epsilon delta tape).length ≤
      5 * f.length.size + 6 * epsilon.den.size + 2 * n + 42 := by
  have h := run_output_size_le f epsilon delta tape
  have he := Encoding.output_length_le (Program.run f epsilon delta tape)
  simp only [Program.encodeOutput] at h
  unfold Program.runEncoded
  omega

end Counting.Algorithm.KarpLuby.ResourceBounds
