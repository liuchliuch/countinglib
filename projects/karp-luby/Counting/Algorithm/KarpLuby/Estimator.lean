import Counting.Algorithm.KarpLuby.Ranking
import Counting.Algorithm.KarpLuby.Dyadic
import Counting.Algorithm.KarpLuby.Imported.Concentration

/-! Exact and bounded moments of the ranked finite-cover estimator on fair tapes. -/
namespace Counting.Algorithm.KarpLuby

open HiddenCircuits.Approximation.SelfReduction

variable {α : Type*} [DecidableEq α] {m : ℕ}

/-- Single padded trial, expressed by unranking and a decidable owner test. -/
def rankedTrial (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D))
    (r : Fin (dyadicSize (mass D))) : ℚ :=
  if h : r.val < mass D then
    if IsOwner D (e.symm ⟨r.val, h⟩).val then dyadicSize (mass D) else 0
  else 0

/-- This implementation has the successful codes counted in `Ranking`. -/
theorem rankedTrial_eq_dyadicValue (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D)) (r : Fin (dyadicSize (mass D))) :
    rankedTrial D e r =
      dyadicValue (fun z => z ∈ paddedOwnerCodes D e (le_dyadicSize (mass D))) r := by
  unfold rankedTrial dyadicValue
  dsimp only
  simp only [mem_paddedOwnerCodes]
  by_cases h : r.val < mass D <;> simp [h]

/-- A real fixed-length tape execution; no non-dyadic uniform source is assumed. -/
def coverTrial (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D))
    (t : CoinTape (dyadicBits (mass D))) : ℚ :=
  rankedTrial D e (decodeTape (dyadicBits (mass D)) t)

theorem mean_coverTrial (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D)) :
    mean (coverTrial D e) = (count D : ℚ) := by
  change mean (fun t => rankedTrial D e (decodeTape (dyadicBits (mass D)) t)) = _
  calc
    _ = mean (rankedTrial D e) := mean_decodeTape _ _
    _ = _ := by
      calc
        _ = mean (dyadicValue (fun z => z ∈ paddedOwnerCodes D e (le_dyadicSize (mass D)))) :=
          mean_congr (rankedTrial_eq_dyadicValue D e)
        _ = _ := by rw [mean_dyadicValue (dyadicSize_pos (mass D))]; simp

theorem secondMoment_coverTrial (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D)) :
    mean (fun t => coverTrial D e t ^ 2) = (dyadicSize (mass D) : ℚ) * count D := by
  calc
    _ = mean (fun r => rankedTrial D e r ^ 2) := mean_decodeTape _ _
    _ = _ := by
      calc
        _ = mean (fun z => dyadicValue (fun z => z ∈ paddedOwnerCodes D e (le_dyadicSize (mass D))) z ^ 2) :=
          mean_congr (fun z => congrArg (fun x : ℚ => x ^ 2) (rankedTrial_eq_dyadicValue D e z))
        _ = _ := by rw [mean_dyadicValue_sq (dyadicSize_pos (mass D))]; simp

/-- The zero-count branch is exact on every random tape. -/
theorem coverTrial_zero (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D)) (h : count D = 0)
    (t : CoinTape (dyadicBits (mass D))) : coverTrial D e t = 0 := by
  have hm : mass D = 0 := (count_eq_zero_iff_mass_eq_zero D).mp h
  simp [coverTrial, rankedTrial, hm]

theorem coverTrial_nonneg (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D))
    (t : CoinTape (dyadicBits (mass D))) : 0 ≤ coverTrial D e t := by
  unfold coverTrial
  erw [rankedTrial_eq_dyadicValue]
  exact dyadicValue_nonneg _ _

/-- Padding increases the second-moment bound by at most a factor two. -/
theorem secondMoment_coverTrial_le (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D)) :
    mean (fun t => coverTrial D e t ^ 2) ≤ 2 * (m : ℚ) * (count D : ℚ)^2 := by
  rw [secondMoment_coverTrial]
  by_cases h : mass D = 0
  · have hc : count D = 0 := (count_eq_zero_iff_mass_eq_zero D).mpr h
    simp [hc]
  · have hq : (dyadicSize (mass D) : ℚ) ≤ 2 * (mass D : ℚ) := by
      exact_mod_cast dyadicSize_le_twice (Nat.pos_of_ne_zero h)
    have hm : (mass D : ℚ) ≤ (m : ℚ) * count D := by
      exact_mod_cast mass_le_mul_count D
    calc
      (dyadicSize (mass D) : ℚ) * count D ≤ (2 * mass D) * count D :=
        mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg _)
      _ ≤ (2 * ((m : ℚ) * count D)) * count D := by gcongr
      _ = _ := by ring

/-- Exact variance, retained separately from its convenient upper bound. -/
theorem variance_coverTrial (D : Fin m → Finset α)
    (e : {p // p ∈ tagged D} ≃ Fin (mass D)) :
    mean (fun t => (coverTrial D e t - count D)^2) =
      (dyadicSize (mass D) : ℚ) * count D - (count D : ℚ)^2 := by
  rw [← mean_coverTrial D e, mean_centered_sq, secondMoment_coverTrial, mean_coverTrial]

end Counting.Algorithm.KarpLuby
