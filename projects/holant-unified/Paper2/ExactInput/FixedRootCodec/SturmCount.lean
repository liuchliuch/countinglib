import Paper2.ExactInput.FixedRootCodec.SturmCountLocal

/-! Sturm's exact distinct-real-root count, including the right endpoint.
The proof combines local chain algebra, the simple-root sign change, and
connectedness of the real line. The chain carries no assumed counting result. -/
namespace Paper2.ExactInput.FixedRootCodec.SturmCount
open scoped BigOperators
open Filter Topology Polynomial
noncomputable section

/-- Count of elements of a finite real set to the left, including the point. -/
def countLE (R : Finset ℝ) (x : ℝ) : ℤ := ∑ r ∈ R, if r ≤ x then 1 else 0

 theorem eventually_indicator_eq (r x : ℝ) (hr : r ≠ x) :
    ∀ᶠ y in 𝓝 x, (if r ≤ y then (1 : ℤ) else 0) = if r ≤ x then 1 else 0 := by
  rcases hr.lt_or_gt with h | h
  · filter_upwards [eventually_gt_nhds h] with y hy
    simp [h.le, hy.le]
  · filter_upwards [eventually_lt_nhds h] with y hy
    simp [not_le.mpr h, not_le.mpr hy]

 theorem eventually_countLE_eq (R : Finset ℝ) (x : ℝ) (hx : x ∉ R) :
    ∀ᶠ y in 𝓝 x, countLE R y = countLE R x := by
  have h : ∀ᶠ y in 𝓝 x, ∀ r ∈ R,
      (if r ≤ y then (1 : ℤ) else 0) = if r ≤ x then 1 else 0 := by
    apply (Finset.eventually_all R).2
    intro r hr
    exact eventually_indicator_eq r x (by intro he; subst r; exact hx hr)
  exact h.mono fun y hy => Finset.sum_congr rfl hy

 theorem eventually_countLE_at_mem (R : Finset ℝ) (x : ℝ) (hx : x ∈ R) :
    ∀ᶠ y in 𝓝 x, countLE R y = countLE R x - if y < x then 1 else 0 := by
  have hc (z : ℝ) : countLE R z = countLE (R.erase x) z + if x ≤ z then 1 else 0 := by
    unfold countLE
    exact (Finset.sum_erase_add _ _ hx).symm
  filter_upwards [eventually_countLE_eq (R.erase x) x (by simp)] with y hy
  rw [hc y, hc x, hy]
  by_cases h : y < x
  · simp [not_le.mpr h, h]
  · simp [le_of_not_gt h, h]

 theorem countLE_difference (R : Finset ℝ) (a b : ℝ) (hab : a ≤ b) :
    countLE R b-countLE R a = ((R.filter fun r => a < r ∧ r ≤ b).card : ℤ) := by
  unfold countLE
  rw [← Finset.sum_sub_distrib, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hra : r ≤ a
  · have hrb := hra.trans hab
    simp [hra, hrb, not_lt.mpr hra]
  · by_cases hrb : r ≤ b
    · simp [hra, hrb, lt_of_not_ge hra]
    · simp [hra, hrb]

namespace Chain

/-- The distinct real roots of the first polynomial. -/
def roots (C : Chain) : Finset ℝ := (C.polynomial 0).roots.toFinset

 theorem mem_roots_iff (C : Chain) (x : ℝ) : x ∈ C.roots ↔ (C.polynomial 0).eval x = 0 := by
  simp [roots, Polynomial.mem_roots C.head_ne, Polynomial.IsRoot]

/-- Variation plus the cumulative root count is locally constant, including
at roots, where the variation takes the right-limit value. -/
 theorem variation_add_count_locally_constant (C : Chain) :
    IsLocallyConstant (fun x => C.doubledVariation x+2*countLE C.roots x) := by
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro x
  by_cases hx : (C.polynomial 0).eval x = 0
  · have hm : x ∈ C.roots := (C.mem_roots_iff x).mpr hx
    filter_upwards [C.eventually_variation_at_root x hx,
      eventually_countLE_at_mem C.roots x hm] with y hv hc
    rw [hv, hc]
    by_cases h : y < x
    · simp [h]; ring
    · simp [h]
  · have hm : x ∉ C.roots := by simpa [C.mem_roots_iff x] using hx
    filter_upwards [C.eventually_variation_eq x hx,
      eventually_countLE_eq C.roots x hm] with y hv hc
    rw [hv, hc]

/-- Exact Sturm count of distinct real roots in `(a,b]`. Both endpoint values
of the chain may contain zeros; the first entry uses its right-limit sign
variation. -/
 theorem count_Ioc (C : Chain) (a b : ℝ) (hab : a ≤ b) :
    C.doubledVariation a-C.doubledVariation b =
      2*((C.roots.filter fun r => a < r ∧ r ≤ b).card : ℤ) := by
  have hc := C.variation_add_count_locally_constant.apply_eq_of_preconnectedSpace a b
  have hd := countLE_difference C.roots a b hab
  linear_combination hc + 2*hd

/-- When the right endpoint is not a root, the same formula counts `(a,b)`. -/
 theorem count_Ioo (C : Chain) (a b : ℝ) (hab : a ≤ b)
    (hb : (C.polynomial 0).eval b ≠ 0) :
    C.doubledVariation a-C.doubledVariation b =
      2*((C.roots.filter fun r => a < r ∧ r < b).card : ℤ) := by
  have hfilter : C.roots.filter (fun r => a < r ∧ r ≤ b) =
      C.roots.filter (fun r => a < r ∧ r < b) := by
    apply Finset.filter_congr
    intro r hr
    have hne : r ≠ b := by
      intro h; subst r; exact hb ((C.mem_roots_iff b).mp hr)
    exact and_congr_right fun _ => le_iff_lt_or_eq.trans (or_iff_left hne)
  simpa [hfilter] using C.count_Ioc a b hab

end Chain
end
end Paper2.ExactInput.FixedRootCodec.SturmCount
