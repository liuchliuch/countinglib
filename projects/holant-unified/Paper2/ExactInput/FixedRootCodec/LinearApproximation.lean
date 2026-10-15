import Paper2.ExactInput.FixedRootCodec.FixedRealMachines
import Paper2.ExactInput.FixedRootCodec.InputHeight
import Paper2.ExactInput.FixedRootCodec.UnaryPrecision

/-! A finite collection of fixed real algebraic constants is approximated by
actual bisection programs. Exact rational sign tests, multiplication and sums
propagate intervals through a variable rational linear combination. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open scoped BigOperators
noncomputable section

def unitEpsilon (k : ℕ) : ℚ := ((2 : ℚ)^k)⁻¹

def unitEpsilonComputes : Computes UnaryBinary.unaryEncoding rationalEncoding unitEpsilon := by
  let initial := pairComputes (identityComputes UnaryBinary.unaryEncoding)
    (constantComputes UnaryBinary.unaryEncoding bisectionEncoding (0,0,1))
  apply congrComputes ((initial.andThen (bisectionComputes [])).andThen epsilonComputes)
  intro k
  change epsilon ((bisect [])^[k] (0,0,1)) = unitEpsilon k
  rw [epsilon_iterate]
  norm_num [epsilon,unitEpsilon]

theorem unitEpsilon_positive (k : ℕ) : 0 < unitEpsilon k := by
  unfold unitEpsilon
  positivity

def scaledInterval (q : ℚ) (t : ℚ × ℚ) : ℚ × ℚ :=
  if q < 0 then (q * t.2,q * t.1) else (q * t.1,q * t.2)

def scaledIntervalComputes {α : Type} {e : Encoding α Bool}
    {q : α → ℚ} {t : α → ℚ × ℚ}
    (u : Computes e rationalEncoding q) (w : Computes e intervalEncoding t) :
    Computes e intervalEncoding (fun x => scaledInterval (q x) (t x)) := by
  let lower := w.andThen (Wiring.firstComputes rationalEncoding rationalEncoding)
  let upper := w.andThen (Wiring.secondComputes rationalEncoding rationalEncoding)
  let positive := pairComputes (BellMachines.rationalProvider.mulComputes u lower)
    (BellMachines.rationalProvider.mulComputes u upper)
  let negative := pairComputes (BellMachines.rationalProvider.mulComputes u upper)
    (BellMachines.rationalProvider.mulComputes u lower)
  exact congrComputes (ifComputes (u.andThen rationalNegativeComputes) negative positive)
    (fun x => by simp only [scaledInterval,Function.comp_apply,decide_eq_true_eq])

theorem scaledInterval_contains (q : ℚ) (t : ℚ × ℚ) (a : ℝ)
    (h : (t.1 : ℝ) ≤ a ∧ a ≤ (t.2 : ℝ)) :
    ((scaledInterval q t).1 : ℝ) ≤ q * a ∧ q * a ≤ (scaledInterval q t).2 := by
  unfold scaledInterval
  split_ifs with hq
  · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast hq.le
    push_cast
    exact ⟨mul_le_mul_of_nonpos_left h.2 hq',mul_le_mul_of_nonpos_left h.1 hq'⟩
  · have hq' : (0 : ℝ) ≤ q := by exact_mod_cast le_of_not_gt hq
    push_cast
    exact ⟨mul_le_mul_of_nonneg_left h.1 hq',mul_le_mul_of_nonneg_left h.2 hq'⟩

theorem scaledInterval_width (q : ℚ) (t : ℚ × ℚ) :
    (scaledInterval q t).2 - (scaledInterval q t).1 = |q| * (t.2 - t.1) := by
  unfold scaledInterval
  split_ifs with hq
  · rw [abs_of_neg hq]
    ring
  · rw [abs_of_nonneg (le_of_not_gt hq)]
    ring

variable {n : ℕ} {a : Fin n → ℝ}

def realLinearApproximation (b : ∀ i, RealBracket (a i)) (k : ℕ) (v : Fin n → ℚ) : ℚ × ℚ :=
  ((∑ i, (scaledInterval (v i) (realApproximation (b i) k)).1) - unitEpsilon k,
    (∑ i, (scaledInterval (v i) (realApproximation (b i) k)).2) + unitEpsilon k)

abbrev precisionVectorEncoding (n : ℕ) := pairEncoding UnaryBinary.unaryEncoding (vectorEncoding n)

def realLinearApproximationComputes (b : ∀ i, RealBracket (a i)) :
    Computes (precisionVectorEncoding n) intervalEncoding
      (fun x => realLinearApproximation b x.1 x.2) := by
  let counter := Wiring.firstComputes UnaryBinary.unaryEncoding (vectorEncoding n)
  let coordinates := Wiring.secondComputes UnaryBinary.unaryEncoding (vectorEncoding n)
  let cells (i : Fin n) := scaledIntervalComputes
    (coordinates.andThen (coordinateComputes n i))
    (counter.andThen (realApproximationComputes (b i)))
  let lower := BellMachines.rationalProvider.sumComputes (precisionVectorEncoding n) n
    (fun x i => (scaledInterval (x.2 i) (realApproximation (b i) x.1)).1)
    (fun i => congrComputes ((cells i).andThen (Wiring.firstComputes _ _)) (fun _ => rfl))
  let upper := BellMachines.rationalProvider.sumComputes (precisionVectorEncoding n) n
    (fun x i => (scaledInterval (x.2 i) (realApproximation (b i) x.1)).2)
    (fun i => congrComputes ((cells i).andThen (Wiring.secondComputes _ _)) (fun _ => rfl))
  let eps := counter.andThen unitEpsilonComputes
  let negEps := BellMachines.rationalProvider.mulComputes eps
    (constantComputes (precisionVectorEncoding n) rationalEncoding (-1))
  exact congrComputes (pairComputes
    (BellMachines.rationalProvider.addComputes lower negEps)
    (BellMachines.rationalProvider.addComputes upper eps))
    (fun x => by simp only [realLinearApproximation,Function.comp_apply,mul_neg_one,
      sub_eq_add_neg])

theorem realLinearApproximation_contains (b : ∀ i, RealBracket (a i)) (k : ℕ) (v : Fin n → ℚ) :
    ((realLinearApproximation b k v).1 : ℝ) < ∑ i, (v i : ℝ) * a i ∧
      (∑ i, (v i : ℝ) * a i) < (realLinearApproximation b k v).2 := by
  have hc (i : Fin n) := scaledInterval_contains (v i) (realApproximation (b i) k) (a i)
    ⟨(realApproximation_contains (b i) k).1.le,(realApproximation_contains (b i) k).2.le⟩
  have hl := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => (hc i).1)
  have hu := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => (hc i).2)
  have he : (0 : ℝ) < unitEpsilon k := by exact_mod_cast unitEpsilon_positive k
  simp only [realLinearApproximation,Rat.cast_sub,Rat.cast_add,Rat.cast_sum]
  constructor <;> linarith

def bracketWidth {x : ℝ} (b : RealBracket x) : ℚ :=
  b.interval.width + 2 * epsilon (intervalState b.interval)

theorem bracketWidth_nonnegative {x : ℝ} (b : RealBracket x) : 0 ≤ bracketWidth b := by
  have h := b.brackets.1
  have he := epsilon_positive (intervalState b.interval) (intervalState_positive _)
  unfold bracketWidth Holant.LocalDrafts.EffectiveAlgebraic.RealIsolation.Interval.width
  linarith

theorem realLinearApproximation_width (b : ∀ i, RealBracket (a i))
    (k B : ℕ) (v : Fin n → ℚ) (hv : ∀ i, rationalBitHeight (v i) ≤ B) :
    (realLinearApproximation b k v).2 - (realLinearApproximation b k v).1 ≤
      (2 : ℚ)^B * ((∑ i, bracketWidth (b i)) + 2) / (2 : ℚ)^k := by
  have cell (i : Fin n) :
      (scaledInterval (v i) (realApproximation (b i) k)).2 -
        (scaledInterval (v i) (realApproximation (b i) k)).1 ≤
      (2 : ℚ)^B * bracketWidth (b i) / (2 : ℚ)^k := by
    rw [scaledInterval_width]
    calc
      _ ≤ |v i| * (bracketWidth (b i) / (2 : ℚ)^k) :=
        mul_le_mul_of_nonneg_left (realApproximation_width (b i) k) (abs_nonneg _)
      _ ≤ (2 : ℚ)^B * (bracketWidth (b i) / (2 : ℚ)^k) :=
        mul_le_mul_of_nonneg_right (rational_abs_le_pow (hv i))
          (div_nonneg (bracketWidth_nonnegative _) (by positivity))
      _ = _ := by ring
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => cell i)
  rw [Finset.sum_sub_distrib,← Finset.sum_div,← Finset.mul_sum] at hs
  have he : 2 * unitEpsilon k ≤ (2 : ℚ)^B * 2 / (2 : ℚ)^k := by
    have hb : (1 : ℚ) ≤ 2^B := one_le_pow₀ (by norm_num)
    unfold unitEpsilon
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2^k)).mpr
    have hn : (2 : ℚ)^k ≠ 0 := by positivity
    field_simp
    linarith
  simp only [realLinearApproximation]
  calc
    _ = ((∑ i, (scaledInterval (v i) (realApproximation (b i) k)).2) -
      ∑ i, (scaledInterval (v i) (realApproximation (b i) k)).1) + 2*unitEpsilon k := by ring
    _ ≤ (2 : ℚ)^B * (∑ i, bracketWidth (b i)) / 2^k + (2 : ℚ)^B*2/2^k :=
      add_le_add hs he
    _ = _ := by ring

theorem bracketWidth_power_bound (b : ∀ i, RealBracket (a i)) :
    ∃ D : ℕ, ((∑ i, bracketWidth (b i)) + 2) ≤ (2 : ℚ)^D := by
  obtain ⟨D,hD⟩ := exists_nat_ge (((∑ i, bracketWidth (b i)) + 2) : ℚ)
  refine ⟨D,hD.trans ?_⟩
  exact_mod_cast (Nat.lt_two_pow_self (n := D)).le

end
end Paper2.ExactInput.FixedRootCodec
