import Paper2.ExactInput.FixedRootCodec.RealApproximation

/-! A polynomial finite machine approximates each fixed real algebraic constant.
The bracket and common denominator are compiled constants. Only the requested
unary precision varies, and the bisection controller charges every round and
all rational endpoint normalization to physical transition counts. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.EffectiveAlgebraic
noncomputable section

def intervalState (I : RealInterval) : BisectionState :=
  (I.lower.num * I.upper.den,I.upper.num * I.lower.den,I.lower.den * I.upper.den)

theorem intervalState_positive (I : RealInterval) : 0 < (intervalState I).2.2 :=
  Nat.mul_pos I.lower.den_pos I.upper.den_pos

theorem intervalState_correct (I : RealInterval) : stateInterval (intervalState I) = I := by
  have hl : (I.lower.den : ℚ) ≠ 0 := by exact_mod_cast I.lower.den_pos.ne'
  have hu : (I.upper.den : ℚ) ≠ 0 := by exact_mod_cast I.upper.den_pos.ne'
  have hlo : (stateInterval (intervalState I)).lower = I.lower := by
    simp only [stateInterval,intervalState,Rat.mkRat_eq_divInt,Rat.divInt_eq_div]
    push_cast
    calc
      _ = (I.lower.num : ℚ) / I.lower.den := by field_simp
      _ = I.lower := Rat.num_div_den _
  have hup : (stateInterval (intervalState I)).upper = I.upper := by
    simp only [stateInterval,intervalState,Rat.mkRat_eq_divInt,Rat.divInt_eq_div]
    push_cast
    calc
      _ = (I.upper.num : ℚ) / I.upper.den := by field_simp
      _ = I.upper := Rat.num_div_den _
  cases I
  simp only [stateInterval] at hlo hup ⊢
  congr 1

abbrev intervalEncoding := pairEncoding rationalEncoding rationalEncoding

def lowerEndpointComputes : Computes bisectionEncoding rationalEncoding
    (fun s => (stateInterval s).lower) :=
  congrComputes ((pairComputes leftComputes denominatorComputes).andThen
    RationalArithmetic.normalizationForwardComputes) (fun _ => rfl)

def upperEndpointComputes : Computes bisectionEncoding rationalEncoding
    (fun s => (stateInterval s).upper) :=
  congrComputes ((pairComputes rightComputes denominatorComputes).andThen
    RationalArithmetic.normalizationForwardComputes) (fun _ => rfl)

def epsilon (s : BisectionState) : ℚ := mkRat 1 s.2.2

def epsilonComputes : Computes bisectionEncoding rationalEncoding epsilon :=
  congrComputes ((pairComputes (constantComputes bisectionEncoding
    IntegerArithmetic.encoding 1) denominatorComputes).andThen
    RationalArithmetic.normalizationForwardComputes) (fun _ => rfl)

def widenedInterval (s : BisectionState) : ℚ × ℚ :=
  ((stateInterval s).lower - epsilon s,(stateInterval s).upper + epsilon s)

def widenedComputes : Computes bisectionEncoding intervalEncoding widenedInterval := by
  let negE := BellMachines.rationalProvider.mulComputes epsilonComputes
    (constantComputes bisectionEncoding rationalEncoding (-1))
  exact congrComputes (pairComputes
    (BellMachines.rationalProvider.addComputes lowerEndpointComputes negE)
    (BellMachines.rationalProvider.addComputes upperEndpointComputes epsilonComputes))
    (fun s => by simp only [widenedInterval,sub_eq_add_neg,mul_neg_one])

def realApproximation {a : ℝ} (b : RealBracket a) (k : ℕ) : ℚ × ℚ :=
  widenedInterval ((bisect b.polynomial)^[k] (intervalState b.interval))

def realApproximationComputes {a : ℝ} (b : RealBracket a) :
    Computes UnaryBinary.unaryEncoding intervalEncoding (realApproximation b) := by
  let initial := pairComputes (identityComputes UnaryBinary.unaryEncoding)
    (constantComputes UnaryBinary.unaryEncoding bisectionEncoding (intervalState b.interval))
  exact congrComputes ((initial.andThen (bisectionComputes b.polynomial)).andThen
    widenedComputes) (fun _ => rfl)

theorem epsilon_positive (s : BisectionState) (hq : 0 < s.2.2) : 0 < epsilon s := by
  simp only [epsilon,Rat.mkRat_eq_divInt,Rat.divInt_eq_div]
  positivity

theorem epsilon_iterate (p : Paper2.ExactInput.RationalPolynomialCode)
    (s : BisectionState) (k : ℕ) :
    epsilon ((bisect p)^[k] s) = epsilon s / (2 : ℚ)^k := by
  simp only [epsilon,bisection_denominator,Rat.mkRat_eq_divInt,Rat.divInt_eq_div]
  push_cast
  simp only [one_div]
  ring

theorem realApproximation_contains {a : ℝ} (b : RealBracket a) (k : ℕ) :
    (realApproximation b k).1 < a ∧ a < (realApproximation b k).2 := by
  have hq : 0 < ((bisect b.polynomial)^[k] (intervalState b.interval)).2.2 := by
    rw [bisection_denominator]
    exact Nat.mul_pos (by positivity) (intervalState_positive _)
  have he : (0 : ℝ) < epsilon ((bisect b.polynomial)^[k] (intervalState b.interval)) :=
    by exact_mod_cast epsilon_positive _ hq
  have hc := b.refine_contains k
  rw [← intervalState_correct b.interval,← interval_iterate _ _ (intervalState_positive _)] at hc
  change ((stateInterval _).lower : ℝ) ≤ a ∧ a ≤ (stateInterval _).upper at hc
  simp only [realApproximation,widenedInterval,Rat.cast_sub,Rat.cast_add]
  constructor <;> linarith [hc.1,hc.2]

theorem realApproximation_width {a : ℝ} (b : RealBracket a) (k : ℕ) :
    (realApproximation b k).2 - (realApproximation b k).1 ≤
      (b.interval.width + 2 * epsilon (intervalState b.interval)) / (2 : ℚ)^k := by
  have hw := b.width_bound k
  have hi : stateInterval ((bisect b.polynomial)^[k] (intervalState b.interval)) =
      RealIsolation.refine b.polynomial b.interval k := by
    simpa only [intervalState_correct] using
      interval_iterate b.polynomial (intervalState b.interval) (intervalState_positive _) k
  rw [← hi] at hw
  simp only [realApproximation,widenedInterval]
  rw [epsilon_iterate]
  change (stateInterval _).upper + _ - ((stateInterval _).lower - _) ≤ _
  unfold Holant.LocalDrafts.EffectiveAlgebraic.RealIsolation.Interval.width at hw
  calc
    _ = (stateInterval ((bisect b.polynomial)^[k] (intervalState b.interval))).width +
      2 * (epsilon (intervalState b.interval) / (2 : ℚ)^k) := by
        unfold Holant.LocalDrafts.EffectiveAlgebraic.RealIsolation.Interval.width
        ring
    _ ≤ b.interval.width / (2 : ℚ)^k +
      2 * (epsilon (intervalState b.interval) / (2 : ℚ)^k) := add_le_add hw (le_refl _)
    _ = _ := by ring

end
end Paper2.ExactInput.FixedRootCodec
