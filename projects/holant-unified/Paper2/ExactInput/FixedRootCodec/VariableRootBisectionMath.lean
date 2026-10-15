import Paper2.ExactInput.FixedRootCodec.VariableRootBisection
import Paper2.ExactInput.FixedRootCodec.FixedRealMachines
import Paper2.ExactInput.FixedRootCodec.ReverseLinear
import Mathlib.Order.Interval.Finset.Fin

/-! Correctness of rank refinement against the actual number of distinct
sorted real roots at or below a rational point. A midpoint equal to a root
is retained as a closed endpoint; the final common-denominator widening
produces a strict open interval. No root-count algorithm is postulated. -/
namespace Paper2.ExactInput.FixedRootCodec.VariableRootBisection
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines GraphPreprocessing
open Holant.LocalDrafts.EffectiveAlgebraic
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

def sortedPrefixCount (roots : Fin d → ℝ) (q : ℚ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => roots i ≤ (q : ℝ))).card

theorem sortedPrefixCount_le_iff (roots : Fin d → ℝ) (hs : StrictMono roots)
    (j : Fin d) (q : ℚ) :
    sortedPrefixCount roots q ≤ j.val ↔ (q : ℝ) < roots j := by
  classical
  constructor
  · intro hc
    by_contra hq
    have hq' : roots j ≤ (q : ℝ) := le_of_not_gt hq
    have hi : Finset.Iic j ⊆ Finset.univ.filter (fun i => roots i ≤ (q : ℝ)) := by
      intro i hi
      simp only [Finset.mem_Iic] at hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hs.monotone hi).trans hq'⟩
    have hk := Finset.card_le_card hi
    rw [Fin.card_Iic] at hk
    change j.val+1 ≤ sortedPrefixCount roots q at hk
    omega
  · intro hq
    have hi : Finset.univ.filter (fun i => roots i ≤ (q : ℝ)) ⊆ Finset.Iio j := by
      intro i hi
      have hr := (Finset.mem_filter.mp hi).2
      apply Finset.mem_Iio.mpr
      by_contra hij
      have hj : j ≤ i := le_of_not_gt hij
      exact (hq.trans_le ((hs.monotone hj).trans hr)).false
    have hk := Finset.card_le_card hi
    rw [Fin.card_Iio] at hk
    exact hk

def intervalHalf (lower : Bool) (I : RealInterval) : RealInterval :=
  if lower then ⟨I.midpoint,I.upper⟩ else ⟨I.lower,I.midpoint⟩

theorem half_interval (lower : Bool) (s : BisectionState) (hq : 0 < s.2.2) :
    stateInterval (half lower s) = intervalHalf lower (stateInterval s) := by
  cases lower <;> simp [half,intervalHalf,stateInterval,double_ratio _ _ hq]
  all_goals exact (interval_midpoint s hq).symm

theorem intervalHalf_width (lower : Bool) (I : RealInterval) :
    (intervalHalf lower I).width = I.width/2 := by
  cases lower <;> simp only [intervalHalf,Bool.false_eq_true,↓reduceIte,
    RealIsolation.Interval.width,RealIsolation.Interval.midpoint] <;> ring

def ClosedContains (s : State n) (r : ℝ) : Prop :=
  ((stateInterval s.2).lower : ℝ) ≤ r ∧ r ≤ (stateInterval s.2).upper

theorem step_contains (count : CountFunction n) (j : ℕ) (s : State n)
    (r : ℝ) (hq : 0 < s.2.2.2) (hs : ClosedContains s r)
    (hcount : ∀ q : ℚ, count s.1 q ≤ j ↔ (q : ℝ) < r) :
    ClosedContains (step count j s) r := by
  have hc := hcount (midpoint s.2)
  unfold ClosedContains at hs ⊢
  dsimp only [step]
  rw [half_interval _ _ hq]
  by_cases h : count s.1 (midpoint s.2) ≤ j
  · simp only [h,decide_true,intervalHalf,↓reduceIte]
    exact ⟨by rw [interval_midpoint s.2 hq]; exact (hc.mp h).le,hs.2⟩
  · simp only [h,decide_false,intervalHalf,Bool.false_eq_true,↓reduceIte]
    refine ⟨hs.1,?_⟩
    rw [interval_midpoint s.2 hq]
    exact le_of_not_gt (fun hm => h (hc.mpr hm))

theorem iterate_contains (count : CountFunction n) (j : ℕ) (s : State n)
    (r : ℝ) (hq : 0 < s.2.2.2) (hs : ClosedContains s r)
    (hcount : ∀ q : ℚ, count s.1 q ≤ j ↔ (q : ℝ) < r) (k : ℕ) :
    ClosedContains ((step count j)^[k] s) r := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    apply step_contains count j _ r
    · rw [iterate_denominator]
      positivity
    · exact ih
    · simpa only [iterate_coefficients] using hcount

theorem step_width (count : CountFunction n) (j : ℕ) (s : State n)
    (hq : 0 < s.2.2.2) :
    (stateInterval (step count j s).2).width = (stateInterval s.2).width/2 := by
  dsimp only [step]
  rw [half_interval _ _ hq,intervalHalf_width]

theorem iterate_width (count : CountFunction n) (j : ℕ) (s : State n)
    (hq : 0 < s.2.2.2) (k : ℕ) :
    (stateInterval ((step count j)^[k] s).2).width =
      (stateInterval s.2).width/(2 : ℚ)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',step_width]
    · rw [ih,pow_succ,div_div]
    · rw [iterate_denominator]
      positivity

theorem iterate_epsilon (count : CountFunction n) (j : ℕ) (s : State n)
    (hq : 0 < s.2.2.2) (k : ℕ) :
    epsilon ((step count j)^[k] s).2 = epsilon s.2/(2 : ℚ)^k := by
  simp only [epsilon,iterate_denominator,Rat.mkRat_eq_divInt,Rat.divInt_eq_div]
  push_cast
  field_simp

def output (count : CountFunction n) (j : ℕ) (k : ℕ) (s : State n) : ℚ × ℚ :=
  widenedInterval ((step count j)^[k] s).2

def outputComputes (count : CountFunction n) (j : ℕ)
    (w : Computes (VariablePolynomial.inputEncoding n) encodingNatBool
      (fun p => count p.1 p.2)) :
    Computes (BoundedIterate.inputEncoding (stateEncoding n)) intervalEncoding
      (fun p => output count j p.1 p.2) :=
  congrComputes (((computes count j w).andThen
    (Wiring.secondComputes (vectorEncoding n) bisectionEncoding)).andThen widenedComputes)
    (fun _ => rfl)

theorem output_contains (count : CountFunction n) (j : ℕ) (k : ℕ) (s : State n)
    (r : ℝ) (hq : 0 < s.2.2.2) (hs : ClosedContains s r)
    (hcount : ∀ q : ℚ, count s.1 q ≤ j ↔ (q : ℝ) < r) :
    ((output count j k s).1 : ℝ) < r ∧ r < (output count j k s).2 := by
  have hc := iterate_contains count j s r hq hs hcount k
  have hd : 0 < (((step count j)^[k] s).2).2.2 := by
    rw [iterate_denominator]
    positivity
  have he : (0 : ℝ) < epsilon (((step count j)^[k] s).2) := by
    exact_mod_cast epsilon_positive _ hd
  simp only [output,widenedInterval,Rat.cast_sub,Rat.cast_add]
  unfold ClosedContains at hc
  constructor <;> linarith [hc.1,hc.2]

theorem output_width (count : CountFunction n) (j : ℕ) (k : ℕ) (s : State n)
    (hq : 0 < s.2.2.2) :
    (output count j k s).2 - (output count j k s).1 =
      ((stateInterval s.2).width+2*epsilon s.2)/(2 : ℚ)^k := by
  simp only [output,widenedInterval]
  rw [iterate_epsilon count j s hq k]
  change (stateInterval _).upper + _ - ((stateInterval _).lower - _) = _
  have hw := iterate_width count j s hq k
  unfold RealIsolation.Interval.width at hw
  unfold RealIsolation.Interval.width
  rw [add_div,mul_div_assoc,← hw]
  ring

def point (count : CountFunction n) (j : ℕ) (k : ℕ) (s : State n) : ℚ :=
  intervalMidpoint (output count j k s)

def pointComputes (count : CountFunction n) (j : ℕ)
    (w : Computes (VariablePolynomial.inputEncoding n) encodingNatBool
      (fun p => count p.1 p.2)) :
    Computes (BoundedIterate.inputEncoding (stateEncoding n)) rationalEncoding
      (fun p => point count j p.1 p.2) :=
  (outputComputes count j w).andThen intervalMidpointComputes

theorem point_error (count : CountFunction n) (j : ℕ) (k : ℕ) (s : State n)
    (r : ℝ) (hq : 0 < s.2.2.2) (hs : ClosedContains s r)
    (hcount : ∀ q : ℚ, count s.1 q ≤ j ↔ (q : ℝ) < r) :
    |(point count j k s : ℝ)-r| <
      (((stateInterval s.2).width+2*epsilon s.2)/(2 : ℚ)^k : ℚ) := by
  have hc := output_contains count j k s r hq hs hcount
  have hw := output_width count j k s hq
  have he : |(point count j k s : ℝ)-r| <
      ((output count j k s).2 : ℝ)-(output count j k s).1 := by
    unfold point intervalMidpoint
    push_cast
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  rw [← Rat.cast_sub,hw] at he
  exact he

/-- Apply the genuine sorted-root count semantics, including a midpoint which
is itself a root; rank j then remains at the upper closed endpoint. -/
theorem sorted_root_output_contains (count : CountFunction n) (j : Fin d)
    (roots : Fin d → ℝ) (hroots : StrictMono roots) (k : ℕ) (s : State n)
    (hq : 0 < s.2.2.2) (hs : ClosedContains s (roots j))
    (hcount : ∀ q : ℚ, count s.1 q = sortedPrefixCount roots q) :
    ((output count j.val k s).1 : ℝ) < roots j ∧ roots j < (output count j.val k s).2 :=
  output_contains count j.val k s (roots j) hq hs
    (fun q => by rw [hcount q]; exact sortedPrefixCount_le_iff roots hroots j q)

end
end Paper2.ExactInput.FixedRootCodec.VariableRootBisection
