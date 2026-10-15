import Counting.Algorithm.KarpLuby.Program

/-!
# Packed fair tapes and independent products

The algorithm's concrete consecutive blocks are an equivalence with a finite
product of independent fair tapes. This identifies the actual executable
estimator with the probability theorem; independence is not an extra assumption.
-/

namespace Counting.Algorithm.KarpLuby

open HiddenCircuits.Approximation.SelfReduction
open scoped BigOperators

/-- Uniform finite probability is invariant under an explicit equivalence. -/
theorem probability_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (E : β → Prop) :
    probability (fun a => E (e a)) = probability E := by
  classical
  exact mean_equiv e (fun b => if E b then 1 else 0)

/-- Partitioning a fixed tape into consecutive blocks is bijective. -/
def chunksEquiv (width blocks : ℕ) :
    CoinTape (blocks * width) ≃ (Fin blocks → CoinTape width) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.curry (Fin blocks) (Fin width) Bool)

@[simp] theorem chunksEquiv_apply (width blocks : ℕ) (tape : CoinTape (blocks * width)) :
    chunksEquiv width blocks tape = Program.coinChunk tape := by
  funext block bit
  change tape (finProdFinEquiv (block, bit)) = tape _
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- Consecutive groups and consecutive trials within each group partition the
whole tape, including when a width or a number of blocks is zero. -/
def productTapesEquiv (width samples groups : ℕ) :
    CoinTape (groups * (samples * width)) ≃ (Fin groups → Fin samples → CoinTape width) :=
  (chunksEquiv (samples * width) groups).trans
    (Equiv.arrowCongr (Equiv.refl (Fin groups)) (chunksEquiv width samples))

@[simp] theorem productTapesEquiv_apply (width samples groups : ℕ)
    (tape : CoinTape (groups * (samples * width))) (g : Fin groups) (s : Fin samples) :
    productTapesEquiv width samples groups tape g s =
      Program.coinChunk (Program.coinChunk tape g) s := by
  change chunksEquiv width samples (chunksEquiv (samples * width) groups tape g) s = _
  simp

namespace Program

variable {n : ℕ}

/-- Rational semantics of one actual fixed-length fair-bit trial. -/
def trialOnTape (cs : List (DNF.Clause n))
    (tape : CoinTape (dyadicBits (totalMass cs))) : ℚ :=
  trial cs (decodeNat (dyadicBits (totalMass cs)) tape)

 theorem mean_trialOnTape (cs : List (DNF.Clause n)) :
    mean (trialOnTape cs) =
      mean (fun i : Fin (dyadicSize (totalMass cs)) => (trial cs i : ℚ)) :=
  mean_decodeTape (dyadicBits (totalMass cs)) (fun i => (trial cs i : ℚ))

 theorem mean_trialOnTape_sq (cs : List (DNF.Clause n)) :
    mean (fun tape => trialOnTape cs tape ^ 2) =
      mean (fun i : Fin (dyadicSize (totalMass cs)) => (trial cs i : ℚ) ^ 2) :=
  mean_decodeTape (dyadicBits (totalMass cs)) (fun i => (trial cs i : ℚ) ^ 2)

/-- Natural accumulation and rational finite averaging have identical values. -/
 theorem naturalAverage_eq_sum (samples : ℕ) (f : Fin samples → ℕ) :
    naturalAverage samples f = (∑ i, (f i : ℚ)) / samples := by
  simp [naturalAverage, List.sum_ofFn, Nat.cast_sum]

 theorem groupAverage_eq_sampleAverage (cs : List (DNF.Clause n)) (samples : ℕ)
    (tape : CoinTape (samples * dyadicBits (totalMass cs))) :
    groupAverage cs samples tape = sampleAverage samples (trialOnTape cs)
      (chunksEquiv (dyadicBits (totalMass cs)) samples tape) := by
  simp [groupAverage, naturalAverage_eq_sum, sampleAverage, trialOnTape]

 theorem groupAverage_nonneg (cs : List (DNF.Clause n)) (samples : ℕ)
    (tape : CoinTape (samples * dyadicBits (totalMass cs))) :
    0 ≤ groupAverage cs samples tape := by
  unfold groupAverage naturalAverage
  positivity

 theorem groupAverage_zero_of_trial_zero (cs : List (DNF.Clause n)) (samples : ℕ)
    (hzero : ∀ r, trial cs r = 0)
    (tape : CoinTape (samples * dyadicBits (totalMass cs))) :
    groupAverage cs samples tape = 0 := by
  simp [groupAverage, naturalAverage, hzero]

 theorem estimate_nonneg (cs : List (DNF.Clause n)) (samples groups : ℕ)
    (tape : CoinTape (randomBitBudget cs samples groups)) :
    0 ≤ estimate cs samples groups tape :=
  median_nonneg _ _ (fun _ => groupAverage_nonneg cs samples _)

 theorem estimate_zero_of_trial_zero (cs : List (DNF.Clause n)) (samples groups : ℕ)
    (hzero : ∀ r, trial cs r = 0)
    (tape : CoinTape (randomBitBudget cs samples groups)) :
    estimate cs samples groups tape = 0 :=
  median_all_zero _ _ (fun _ => groupAverage_zero_of_trial_zero cs samples hzero _)

/-- Zero mass is returned exactly on every tape, including empty sample budgets. -/
 theorem estimate_of_zero_mass (cs : List (DNF.Clause n)) (samples groups : ℕ)
    (hzero : totalMass cs = 0)
    (tape : CoinTape (randomBitBudget cs samples groups)) :
    estimate cs samples groups tape = 0 :=
  estimate_zero_of_trial_zero cs samples groups (trial_of_zero_mass cs hzero) tape

 theorem run_nonneg (f : DNF.Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (requestedBudget f epsilon delta)) :
    0 ≤ run f epsilon delta tape :=
  estimate_nonneg _ _ _ tape

/-- The executable program agrees pointwise with the independent-product
estimator after the concrete tape has been regrouped. -/
 theorem estimate_eq_amplifiedEstimate (cs : List (DNF.Clause n)) (samples k : ℕ)
    (tape : CoinTape (randomBitBudget cs samples (2 * k))) :
    estimate cs samples (2 * k) tape = amplifiedEstimate (trialOnTape cs) samples k
      (productTapesEquiv (dyadicBits (totalMass cs)) samples (2 * k) tape) := by
  unfold estimate amplifiedEstimate
  congr 1
  funext g
  rw [groupAverage_eq_sampleAverage]
  congr 1
  funext s
  rw [chunksEquiv_apply]
  exact (productTapesEquiv_apply _ _ _ tape g s).symm

/-- The actual bounded-tape program has the PAC bound whenever its actual
single-trial first and second moments satisfy the cover estimates. -/
 theorem estimate_failure_of_moments (cs : List (DNF.Clause n))
    (C : ℚ) (m samples k : ℕ) (ε : ℚ)
    (hmean : mean (fun i : Fin (dyadicSize (totalMass cs)) => (trial cs i : ℚ)) = C)
    (hsecond : mean (fun i : Fin (dyadicSize (totalMass cs)) => (trial cs i : ℚ) ^ 2) ≤
      2 * (m : ℚ) * C ^ 2)
    (hC : 0 < C) (hsamples : 0 < samples) (hε : 0 < ε)
    (hbudget : 144 * (m : ℚ) ≤ (samples : ℚ) * ε ^ 2) :
    probability (fun tape : CoinTape (randomBitBudget cs samples (2 * k)) =>
      ε * C < |estimate cs samples (2 * k) tape - C|) ≤ 1 / (2 ^ k : ℚ) := by
  have hm : mean (trialOnTape cs) = C := (mean_trialOnTape cs).trans hmean
  have hs : mean (fun tape => trialOnTape cs tape ^ 2) ≤ 2 * (m : ℚ) * C ^ 2 := by
    rw [mean_trialOnTape_sq]
    exact hsecond
  have hp := amplifiedEstimate_failure (trialOnTape cs) C m samples k ε
    hm hs hC hsamples hε hbudget
  calc
    _ = probability (fun r : Fin (2 * k) → Fin samples → CoinTape (dyadicBits (totalMass cs)) =>
        ε * C < |amplifiedEstimate (trialOnTape cs) samples k r - C|) := by
      simp_rw [estimate_eq_amplifiedEstimate]
      exact probability_equiv (α := CoinTape (randomBitBudget cs samples (2 * k)))
        (productTapesEquiv (dyadicBits (totalMass cs)) samples (2 * k))
        (fun r => ε * C < |amplifiedEstimate (trialOnTape cs) samples k r - C|)
    _ ≤ _ := hp

/-- Success-probability form for the actual packed-tape execution. -/
 theorem estimate_success_of_moments (cs : List (DNF.Clause n))
    (C : ℚ) (m samples k : ℕ) (ε : ℚ)
    (hmean : mean (fun i : Fin (dyadicSize (totalMass cs)) => (trial cs i : ℚ)) = C)
    (hsecond : mean (fun i : Fin (dyadicSize (totalMass cs)) => (trial cs i : ℚ) ^ 2) ≤
      2 * (m : ℚ) * C ^ 2)
    (hC : 0 < C) (hsamples : 0 < samples) (hε : 0 < ε)
    (hbudget : 144 * (m : ℚ) ≤ (samples : ℚ) * ε ^ 2) :
    1 - 1 / (2 ^ k : ℚ) ≤ probability
      (fun tape : CoinTape (randomBitBudget cs samples (2 * k)) =>
        |estimate cs samples (2 * k) tape - C| ≤ ε * C) := by
  have hf := estimate_failure_of_moments cs C m samples k ε hmean hsecond hC hsamples hε hbudget
  have hc := probability_compl
    (fun tape : CoinTape (randomBitBudget cs samples (2 * k)) =>
      ε * C < |estimate cs samples (2 * k) tape - C|)
  simp only [not_lt] at hc
  linarith

end Program
end Counting.Algorithm.KarpLuby
