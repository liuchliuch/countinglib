import Paper2.ExactInput.FixedRootCodec.SturmCountAlgebra
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Instances.Sign

/-! Local constancy and the simple-root jump of the exact Sturm variation. -/
namespace Paper2.ExactInput.FixedRootCodec.SturmCount
open scoped BigOperators
open Filter Topology Polynomial SignType
noncomputable section

/-- Positive derivative at a root determines the local sign; this follows
from the actual difference-quotient limit. -/
theorem eventually_sign_eq_of_positive_derivative {f : ℝ → ℝ} {x d : ℝ}
    (hf : HasDerivAt f d x) (hd : 0 < d) (hx : f x = 0) :
    ∀ᶠ y in 𝓝 x, sign (f y) = sign (y-x) := by
  rw [← nhdsNE_sup_pure x, eventually_sup]
  refine ⟨?_, by simp [hx]⟩
  filter_upwards [hf.tendsto_slope.eventually (eventually_gt_nhds hd)] with y hy
  have hp : 0 < f y/(y-x) := by simpa [slope_def_field, hx] using hy
  rcases div_pos_iff.mp hp with h | h
  · rw [sign_pos h.1, sign_pos h.2]
  · rw [sign_neg h.1, sign_neg h.2]

 theorem eventually_sign_eq_of_negative_derivative {f : ℝ → ℝ} {x d : ℝ}
    (hf : HasDerivAt f d x) (hd : d < 0) (hx : f x = 0) :
    ∀ᶠ y in 𝓝 x, sign (f y) = sign (x-y) := by
  have hp := eventually_sign_eq_of_positive_derivative hf.neg
    (neg_pos.mpr hd) (by simp [hx])
  filter_upwards [hp] with y hy
  have he := congrArg (fun s : SignType => -s) hy
  change -sign (-f y) = -sign (y-x) at he
  calc
    sign (f y) = -sign (y-x) := by simpa only [Left.sign_neg, neg_neg] using he
    _ = sign (x-y) := by rw [← Left.sign_neg, neg_sub]

 theorem eventually_integerSign_eq (p : ℝ[X]) (x : ℝ) (hx : p.eval x ≠ 0) :
    ∀ᶠ y in 𝓝 x, integerSign (p.eval y) = integerSign (p.eval x) := by
  have h : ContinuousAt (fun y => sign (p.eval y)) x :=
    (continuousAt_sign_of_ne_zero hx).comp
      (f := fun y : ℝ => p.eval y) (p.hasDerivAt x).continuousAt
  have he : ∀ᶠ y in 𝓝 x, sign (p.eval y) = sign (p.eval x) := by
    simpa only [ContinuousAt, nhds_discrete, Filter.tendsto_pure] using h
  exact he.mono fun _ hy => congrArg SignType.cast hy

/-- Near a simple root the product with the derivative sign is negative on
its left, zero at the root, and positive on its right. -/
theorem eventually_root_crossing (p : ℝ[X]) (x : ℝ) (hx : p.eval x = 0)
    (hd : p.derivative.eval x ≠ 0) :
    ∀ᶠ y in 𝓝 x,
      integerSign (p.eval y) * integerSign (p.derivative.eval x) =
        (if y < x then -1 else if y = x then 0 else 1) ∧
      (p.eval y = 0 ↔ y = x) := by
  rcases hd.lt_or_gt with hn | hp
  · have hs := eventually_sign_eq_of_negative_derivative (p.hasDerivAt x) hn hx
    filter_upwards [hs] with y hy
    have hz : p.eval y = 0 ↔ y = x := by
      rw [← sign_eq_zero_iff, hy, sign_eq_zero_iff, sub_eq_zero, eq_comm]
    refine ⟨?_, hz⟩
    rcases lt_trichotomy y x with h | h | h
    · simp [integerSign, hy, sign_neg hn, sign_pos (sub_pos.mpr h), h]
    · simp [h, integerSign, hx]
    · simp [integerSign, hy, sign_neg hn, sign_neg (sub_neg.mpr h),
        not_lt.mpr h.le, ne_of_gt h]
  · have hs := eventually_sign_eq_of_positive_derivative (p.hasDerivAt x) hp hx
    filter_upwards [hs] with y hy
    have hz : p.eval y = 0 ↔ y = x := by
      rw [← sign_eq_zero_iff, hy, sign_eq_zero_iff, sub_eq_zero]
    refine ⟨?_, hz⟩
    rcases lt_trichotomy y x with h | h | h
    · simp [integerSign, hy, sign_pos hp, sign_neg (sub_neg.mpr h), h]
    · simp [h, integerSign, hx]
    · simp [integerSign, hy, sign_pos hp, sign_pos (sub_pos.mpr h),
        not_lt.mpr h.le, ne_of_gt h]

namespace Chain

 theorem eventually_signs_fixed (C : Chain) (x : ℝ) :
    ∀ᶠ y in 𝓝 x, ∀ i ≤ C.tailLength+1,
      C.signs x i ≠ 0 → C.signs y i = C.signs x i := by
  have h : ∀ᶠ y in 𝓝 x, ∀ i ∈ Finset.range (C.tailLength+2),
      C.signs x i ≠ 0 → C.signs y i = C.signs x i := by
    apply (Finset.eventually_all _).2
    intro i hi
    by_cases hz : C.signs x i = 0
    · exact Eventually.of_forall fun _ hn => False.elim (hn hz)
    · have hp : (C.polynomial i).eval x ≠ 0 := by
        simpa [signs, integerSign_eq_zero_iff] using hz
      exact (eventually_integerSign_eq (C.polynomial i) x hp).mono fun _ hy _ => hy
  exact h.mono fun y hy i hi => hy i (Finset.mem_range.mpr (by omega))

 theorem variation_change (C : Chain) (x y : ℝ)
    (hfixed : ∀ i ≤ C.tailLength+1, C.signs x i ≠ 0 → C.signs y i = C.signs x i) :
    C.doubledVariation y-C.doubledVariation x =
      -(C.signs y 0-C.signs x 0)*C.signs x 1 -
        (if (C.polynomial 0).eval y = 0 then 1 else 0) +
        (if (C.polynomial 0).eval x = 0 then 1 else 0) := by
  have hs := adjacent_product_change C.tailLength (C.signs x) (C.signs y)
    hfixed (C.signs_last_ne x) (C.signs_adjacent x) (C.signs_opposite x)
  unfold doubledVariation
  simp only [Finset.sum_sub_distrib]
  linear_combination -hs

/-- At a nonroot the doubled variation is locally constant. -/
 theorem eventually_variation_eq (C : Chain) (x : ℝ)
    (hx : (C.polynomial 0).eval x ≠ 0) :
    ∀ᶠ y in 𝓝 x, C.doubledVariation y = C.doubledVariation x := by
  filter_upwards [C.eventually_signs_fixed x] with y hy
  have hz : C.signs x 0 ≠ 0 := by simpa [signs, integerSign_eq_zero_iff] using hx
  have h0 := hy 0 (by omega) hz
  have hz' : (C.polynomial 0).eval y ≠ 0 := by
    have : C.signs y 0 ≠ 0 := by rw [h0]; exact hz
    simpa [signs, integerSign_eq_zero_iff] using this
  have hv := C.variation_change x y hy
  simp only [h0, sub_self, neg_zero, zero_mul, ite_eq_right hx, ite_eq_right hz'] at hv
  omega

/-- At a head root the variation has its right-limit value and its left value
is two larger. This also covers evaluating the sequence at the root itself. -/
 theorem eventually_variation_at_root (C : Chain) (x : ℝ)
    (hx : (C.polynomial 0).eval x = 0) :
    ∀ᶠ y in 𝓝 x,
      C.doubledVariation y = C.doubledVariation x + if y < x then 2 else 0 := by
  have hd : (C.polynomial 0).derivative.eval x ≠ 0 := by
    rw [← C.derivative]
    exact C.adjacent 0 (by omega) x hx
  filter_upwards [C.eventually_signs_fixed x,
    eventually_root_crossing (C.polynomial 0) x hx hd] with y hy hc
  have hv := C.variation_change x y hy
  have h0 : C.signs x 0 = 0 := by simp [signs, hx]
  have hp : C.signs y 0*C.signs x 1 =
      (if y < x then -1 else if y = x then 0 else 1) := by
    simpa [signs, C.derivative] using hc.1
  simp only [h0, sub_zero, neg_mul, hp, ite_eq_left hx] at hv
  by_cases hlt : y < x
  · have hne : y ≠ x := ne_of_lt hlt
    simp [hlt, hc.2, hne] at hv ⊢
    omega
  · by_cases heq : y = x
    · subst y; simp
    · simp [hlt, hc.2, heq] at hv ⊢
      omega

end Chain
end
end Paper2.ExactInput.FixedRootCodec.SturmCount
