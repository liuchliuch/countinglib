import Counting.Algorithm.KarpLuby.Imported.FiniteMean
import Mathlib.Data.Nat.Size

/-!
# Fixed-length fair-bit sampling

A tape is decoded by recursive binary arithmetic, rather than by enumeration of
all tapes. The resulting equivalence transports the imported finite uniform
mean. Padding a positive mass to `2 ^ Nat.size M` uses at most twice that mass.
-/

namespace Counting.Algorithm.KarpLuby

open scoped BigOperators
open HiddenCircuits.Approximation.SelfReduction

/-- Exactly `b` independently supplied fair Boolean choices. -/
abbrev CoinTape (b : ℕ) := Fin b → Bool

/-- Executable binary decoding, with the first tape bit most significant. -/
def decodeTape : (b : ℕ) → CoinTape b ≃ Fin (2 ^ b)
  | 0 =>
    { toFun := fun _ => ⟨0, by decide⟩
      invFun := fun _ => Fin.elim0
      left_inv := fun _ => funext fun i => Fin.elim0 i
      right_inv := fun i => Fin.ext (by have := i.isLt; simp at this; omega) }
  | b + 1 =>
    (Fin.consEquiv (fun _ : Fin (b + 1) => Bool)).symm.trans
      ((Equiv.prodCongr finTwoEquiv.symm (decodeTape b)).trans
        (finProdFinEquiv.trans (finCongr (by simp [pow_succ, Nat.mul_comm]))))

/-- Natural-number result of the executable tape decoder. -/
def decodeNat (b : ℕ) (t : CoinTape b) : ℕ := (decodeTape b t).val

@[simp] theorem decodeNat_zero (t : CoinTape 0) : decodeNat 0 t = 0 := rfl

/-- One recursive decoding step, showing the binary arithmetic performed. -/
theorem decodeNat_succ (b : ℕ) (t : CoinTape (b + 1)) :
    decodeNat (b + 1) t = decodeNat b (Fin.tail t) + 2 ^ b * (t 0).toNat := by
  cases h : t 0 <;> simp [decodeNat, decodeTape, Fin.consEquiv, finTwoEquiv,
    finProdFinEquiv, h]

 theorem decodeNat_lt (b : ℕ) (t : CoinTape b) : decodeNat b t < 2 ^ b :=
  (decodeTape b t).isLt

 theorem decodeTape_bijective (b : ℕ) : Function.Bijective (decodeTape b) :=
  (decodeTape b).bijective

@[simp] theorem card_coinTape (b : ℕ) : Fintype.card (CoinTape b) = 2 ^ b := by
  simp [CoinTape]

/-- Decoding preserves the actual finite uniform distribution on fair tapes. -/
theorem mean_decodeTape (b : ℕ) (f : Fin (2 ^ b) → ℚ) :
    mean (fun t : CoinTape b => f (decodeTape b t)) = mean f :=
  mean_equiv (decodeTape b) f

/-- Number of random bits used by a padded single trial. -/
def dyadicBits (M : ℕ) : ℕ := Nat.size M

/-- Size of the dyadic sampling space, including rejected padding positions. -/
def dyadicSize (M : ℕ) : ℕ := 2 ^ dyadicBits M

 theorem dyadicSize_pos (M : ℕ) : 0 < dyadicSize M := by
  unfold dyadicSize
  positivity

 theorem lt_dyadicSize (M : ℕ) : M < dyadicSize M := Nat.lt_size_self M

 theorem le_dyadicSize (M : ℕ) : M ≤ dyadicSize M := (lt_dyadicSize M).le

/-- Padding costs at most a factor two, including when `M` is a power of two. -/
theorem dyadicSize_le_twice {M : ℕ} (hM : 0 < M) : dyadicSize M ≤ 2 * M := by
  have hs : 0 < Nat.size M := Nat.size_pos.mpr hM
  have hp : 2 ^ (Nat.size M - 1) ≤ M := Nat.lt_size.mp (by omega)
  have he : Nat.size M = (Nat.size M - 1) + 1 := by omega
  unfold dyadicSize dyadicBits
  rw [he, pow_succ]
  omega

@[simp] theorem dyadicBits_zero : dyadicBits 0 = 0 := rfl
@[simp] theorem dyadicSize_zero : dyadicSize 0 = 1 := rfl

/-- A padded event estimator. This executable function returns an integer rational. -/
def dyadicValue {q : ℕ} (A : Fin q → Prop) [DecidablePred A] (r : Fin q) : ℚ :=
  if A r then q else 0

 theorem dyadicValue_nonneg {q : ℕ} (A : Fin q → Prop) [DecidablePred A]
    (r : Fin q) : 0 ≤ dyadicValue A r := by
  simp only [dyadicValue]
  split_ifs <;> positivity

 theorem dyadicValue_le {q : ℕ} (A : Fin q → Prop) [DecidablePred A]
    (r : Fin q) : dyadicValue A r ≤ q := by
  simp only [dyadicValue]
  split_ifs <;> simp

/-- The event cardinality gives the first moment with no probabilistic assumption. -/
theorem mean_dyadicValue {q : ℕ} (hq : 0 < q) (A : Fin q → Prop) [DecidablePred A] :
    mean (dyadicValue A) = (Finset.univ.filter A).card := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  unfold mean dyadicValue
  rw [← Finset.sum_filter]
  simp [hq']

/-- Exact second moment of the event estimator. -/
theorem mean_dyadicValue_sq {q : ℕ} (hq : 0 < q) (A : Fin q → Prop)
    [DecidablePred A] :
    mean (fun r => dyadicValue A r ^ 2) = (q : ℚ) * (Finset.univ.filter A).card := by
  calc
    mean (fun r => dyadicValue A r ^ 2) = mean (fun r => (q : ℚ) * dyadicValue A r) := by
      apply mean_congr
      intro r
      simp only [dyadicValue]
      split_ifs <;> ring
    _ = (q : ℚ) * mean (dyadicValue A) := mean_const_mul _ _
    _ = _ := by rw [mean_dyadicValue hq A]

/-- The same exact moments hold for the concrete fair-bit execution. -/
theorem tape_moments (b : ℕ) (A : Fin (2 ^ b) → Prop) [DecidablePred A] :
    mean (fun t : CoinTape b => dyadicValue A (decodeTape b t)) =
        (Finset.univ.filter A).card ∧
    mean (fun t : CoinTape b => dyadicValue A (decodeTape b t) ^ 2) =
        (2 ^ b : ℚ) * (Finset.univ.filter A).card := by
  constructor
  · rw [mean_decodeTape, mean_dyadicValue (by positivity)]
  · rw [mean_decodeTape b (fun r => dyadicValue A r ^ 2),
      mean_dyadicValue_sq (by positivity)]
    norm_cast

end Counting.Algorithm.KarpLuby
