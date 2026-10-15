import Counting.Algorithm.KarpLuby.Estimator
import Counting.Algorithm.KarpLuby.Confidence
import Counting.Algorithm.KarpLuby.Parameters

/-!
# Rational-parameter PAC guarantee for a ranked finite cover

The random source is an explicit product of finite Boolean tapes. The ranking
is an input to this abstract interface; an executable frontend must provide its
own ranking and its own runtime refinement. Every theorem also covers empty
covers, for which all tapes return exactly zero.
-/

namespace Counting.Algorithm.KarpLuby

open HiddenCircuits.Approximation.SelfReduction

variable {α : Type*} [DecidableEq α] {m : ℕ}

/-- Independent fixed-width trial tapes, arranged into independent groups. -/
abbrev CoverTapes (D : Fin m → Finset α) (epsilon delta : ℚ) :=
  Fin (2 * confidenceGroups delta) → Fin (samples m epsilon) →
    CoinTape (dyadicBits (mass D))

/-- Exact number of Boolean coordinates in the abstract estimator's input. -/
def coverTapeBits (D : Fin m → Finset α) (epsilon delta : ℚ) : ℕ :=
  2 * confidenceGroups delta * (samples m epsilon * dyadicBits (mass D))

/-- Median of independent sample averages with budgets computed from rationals. -/
def coverEstimate (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D)) (epsilon delta : ℚ)
    (tapes : CoverTapes D epsilon delta) : ℚ :=
  amplifiedEstimate (coverTrial D e) (samples m epsilon) (confidenceGroups delta) tapes

omit [DecidableEq α] in
/-- The finite sample space has exactly one state per assignment of the budgeted bits. -/
theorem card_coverTapes (D : Fin m → Finset α) (epsilon delta : ℚ) :
    Fintype.card (CoverTapes D epsilon delta) = 2 ^ coverTapeBits D epsilon delta := by
  simp [CoverTapes, CoinTape, coverTapeBits, ← pow_mul, Nat.mul_comm, Nat.mul_assoc]

/-- The estimator is always a nonnegative rational, without promises on the request. -/
theorem coverEstimate_nonneg (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D)) (epsilon delta : ℚ)
    (tapes : CoverTapes D epsilon delta) : 0 ≤ coverEstimate D e epsilon delta tapes :=
  amplifiedEstimate_nonneg _ _ _ (coverTrial_nonneg D e) tapes

/-- Zero union count is recognized exactly, on every tape and for every request. -/
theorem coverEstimate_zero (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D)) (epsilon delta : ℚ)
    (h : count D = 0) (tapes : CoverTapes D epsilon delta) :
    coverEstimate D e epsilon delta tapes = 0 :=
  amplifiedEstimate_zero _ _ _ (coverTrial_zero D e h) tapes

/-- The first-moment and second-moment facts give a complete relative-error bound,
including the exact-zero branch. No upper bound on positive epsilon is needed. -/
theorem coverEstimate_failure_dyadic (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D)) (epsilon delta : ℚ)
    (he : 0 < epsilon) :
    probability (fun tapes : CoverTapes D epsilon delta =>
      epsilon * (count D : ℚ) < |coverEstimate D e epsilon delta tapes - count D|) ≤
        1 / (2 ^ confidenceGroups delta : ℚ) := by
  by_cases hc : count D = 0
  · simp only [coverEstimate_zero D e epsilon delta hc, hc, Nat.cast_zero, mul_zero,
      sub_zero, abs_zero, lt_self_iff_false, probability_false]
    positivity
  · have hC : 0 < (count D : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    have hm : 0 < m := by
      have hb := (count_le_mass D).trans (mass_le_mul_count D)
      by_contra h
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
      have hmul : m * count D = 0 :=
        (congrArg (fun a : ℕ => a * count D) hm0).trans (Nat.zero_mul _)
      exact hc (Nat.eq_zero_of_le_zero (hb.trans_eq hmul))
    exact amplifiedEstimate_failure (coverTrial D e) (count D) m
      (samples m epsilon) (confidenceGroups delta) epsilon
      (mean_coverTrial D e) (secondMoment_coverTrial_le D e) hC
      (samples_pos hm epsilon) he (samples_accuracy_budget m he)

/-- The concrete confidence budget bounds failure by the requested positive delta. -/
theorem coverEstimate_failure (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D)) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    probability (fun tapes : CoverTapes D epsilon delta =>
      epsilon * (count D : ℚ) < |coverEstimate D e epsilon delta tapes - count D|) ≤
        delta :=
  (coverEstimate_failure_dyadic D e epsilon delta he).trans (confidenceGroups_failure_le hd)

/-- PAC success form on the actual independent finite product of fair tapes. -/
theorem coverEstimate_success (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D)) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    1 - delta ≤ probability (fun tapes : CoverTapes D epsilon delta =>
      |coverEstimate D e epsilon delta tapes - count D| ≤ epsilon * (count D : ℚ)) := by
  have hf := coverEstimate_failure D e epsilon delta he hd
  have hc := probability_compl (fun tapes : CoverTapes D epsilon delta =>
    epsilon * (count D : ℚ) < |coverEstimate D e epsilon delta tapes - count D|)
  simp only [not_lt] at hc
  linarith

/-- The equivalent multiplicative interval formulation of the PAC guarantee. -/
theorem coverEstimate_success_interval (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D)) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    1 - delta ≤ probability (fun tapes : CoverTapes D epsilon delta =>
      (1 - epsilon) * (count D : ℚ) ≤ coverEstimate D e epsilon delta tapes ∧
      coverEstimate D e epsilon delta tapes ≤ (1 + epsilon) * (count D : ℚ)) := by
  apply (coverEstimate_success D e epsilon delta he hd).trans
  apply probability_mono
  intro tapes ht
  obtain ⟨hl, hu⟩ := abs_le.mp ht
  constructor <;> linarith

end Counting.Algorithm.KarpLuby
