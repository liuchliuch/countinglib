import Paper2.ExactInput.RootOutputSize
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Floor.Ring

/-! Quantitative, strictly open rational rectangles. The widened floor interval
keeps a root strictly inside even when a real/imaginary coordinate lies on a grid
line. Isolation follows from an explicit separation bound; proving the required
polynomial separation exponent for arbitrary fixed-field answers remains open. -/
namespace Paper2.ExactInput
open Paper2.Algebraic Polynomial

noncomputable def gridLower (a : ℝ) (Q : ℕ) : ℚ :=
  ((⌊(Q : ℝ) * a⌋ - 1 : ℤ) : ℚ) / Q

noncomputable def gridUpper (a : ℝ) (Q : ℕ) : ℚ :=
  ((⌊(Q : ℝ) * a⌋ + 2 : ℤ) : ℚ) / Q

lemma grid_contains (a : ℝ) {Q : ℕ} (hQ : 0 < Q) :
    (gridLower a Q : ℝ) < a ∧ a < (gridUpper a Q : ℝ) := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlo := Int.floor_le ((Q : ℝ) * a)
  have hhi : (Q : ℝ) * a < (⌊(Q : ℝ) * a⌋ : ℝ) + 1 :=
    (Int.floor_le_iff).mp (le_refl _)
  simp only [gridLower, gridUpper]
  push_cast
  constructor
  · apply (div_lt_iff₀ hQ').mpr
    nlinarith
  · apply (lt_div_iff₀ hQ').mpr
    nlinarith

lemma grid_width (a : ℝ) {Q : ℕ} (hQ : 0 < Q) :
    (gridUpper a Q : ℝ) - (gridLower a Q : ℝ) = 3 / Q := by
  simp only [gridLower, gridUpper]
  push_cast
  ring

noncomputable def gridRectangle (z : ℂ) (Q : ℕ) : RationalRectangle :=
  ⟨gridLower z.re Q, gridUpper z.re Q, gridLower z.im Q, gridUpper z.im Q⟩

theorem gridRectangle_contains (z : ℂ) {Q : ℕ} (hQ : 0 < Q) :
    (gridRectangle z Q).Contains z :=
  ⟨(grid_contains z.re hQ).1, (grid_contains z.re hQ).2,
    (grid_contains z.im hQ).1, (grid_contains z.im hQ).2⟩

/-- Every point in the rectangle is within six grid steps of the chosen root. -/
theorem gridRectangle_near {z w : ℂ} {Q : ℕ} (hQ : 0 < Q)
    (hw : (gridRectangle z Q).Contains w) : ‖w - z‖ < 6 / Q := by
  have hz := gridRectangle_contains z hQ
  have hre := grid_width z.re hQ
  have him := grid_width z.im hQ
  change (gridLower z.re Q : ℝ) < w.re ∧ w.re < (gridUpper z.re Q : ℝ) ∧
    (gridLower z.im Q : ℝ) < w.im ∧ w.im < (gridUpper z.im Q : ℝ) at hw
  change (gridLower z.re Q : ℝ) < z.re ∧ z.re < (gridUpper z.re Q : ℝ) ∧
    (gridLower z.im Q : ℝ) < z.im ∧ z.im < (gridUpper z.im Q : ℝ) at hz
  have hreal : |w.re - z.re| < 3 / Q := abs_lt.mpr ⟨by linarith [hw.1, hz.2.1], by linarith [hw.2.1, hz.1]⟩
  have himag : |w.im - z.im| < 3 / Q := abs_lt.mpr ⟨by linarith [hw.2.2.1, hz.2.2.2], by linarith [hw.2.2.2, hz.2.2.1]⟩
  have hnorm := Complex.norm_le_abs_re_add_abs_im (w - z)
  simp only [Complex.sub_re, Complex.sub_im] at hnorm
  calc
    ‖w - z‖ ≤ |w.re - z.re| + |w.im - z.im| := hnorm
    _ < 3 / (Q : ℝ) + 3 / Q := add_lt_add hreal himag
    _ = 6 / Q := by ring

/-- Explicit root separation suffices for genuine unique-root isolation. This is
not asserted as a polynomial separation theorem. -/
theorem gridRectangle_isolates (p : ℚ[X]) (z : ℂ) {Q : ℕ} (hQ : 0 < Q)
    (separated : ∀ w : ℂ, aeval w p = 0 → w ≠ z → 6 / (Q : ℝ) ≤ ‖w - z‖) :
    ∀ w : ℂ, (gridRectangle z Q).Contains w → aeval w p = 0 → w = z := by
  intro w hw hr
  by_contra hne
  exact (not_lt_of_ge (separated w hr hne)) (gridRectangle_near hQ hw)

/-- Dense monic/irreducible polynomial plus a separated grid box gives exactly
our public strict descriptor predicate, including roots on rational grid lines. -/
theorem grid_minimal_descriptor (p : ℚ[X]) (z : ℂ) {Q : ℕ} (hQ : 0 < Q)
    (hm : p.Monic) (hi : Irreducible p) (hz : aeval z p = 0)
    (separated : ∀ w : ℂ, aeval w p = 0 → w ≠ z → 6 / (Q : ℝ) ≤ ‖w - z‖) :
    (RootCode.mk (densePolynomialCode p) (gridRectangle z Q)).MinimalRepresents z := by
  have hp : (RootCode.mk (densePolynomialCode p) (gridRectangle z Q)).polynomial = p :=
    densePolynomialCode_polynomial p
  refine ⟨⟨?_, gridRectangle_contains z hQ, ?_, ?_⟩, ?_, ?_⟩
  · rw [hp]; exact hm.ne_zero
  · rw [hp]; exact hz
  · intro w hw hr
    exact gridRectangle_isolates p z hQ separated w hw (by simpa only [hp] using hr)
  · rw [hp]; exact hm
  · rw [hp]; exact hi

/-- A coordinate bound controls the unnormalized floor integer explicitly. -/
theorem floor_grid_natAbs_le (a : ℝ) (Q R : ℕ) (ha : |a| ≤ R) :
    (⌊(Q : ℝ) * a⌋ : ℤ).natAbs ≤ Q * R + 1 := by
  have hlo := Int.floor_le ((Q : ℝ) * a)
  have hhi : (Q : ℝ) * a < (⌊(Q : ℝ) * a⌋ : ℝ) + 1 :=
    (Int.floor_le_iff).mp (le_refl _)
  have hbounds := abs_le.mp ha
  have hQ : (0 : ℝ) ≤ Q := by positivity
  have hupper := mul_le_mul_of_nonneg_left hbounds.2 hQ
  have hlower := mul_le_mul_of_nonneg_left hbounds.1 hQ
  have habs : |(⌊(Q : ℝ) * a⌋ : ℝ)| ≤ (Q : ℝ) * R + 1 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have habs' : ((⌊(Q : ℝ) * a⌋ : ℤ).natAbs : ℝ) ≤ (Q : ℝ) * R + 1 := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using habs
  exact_mod_cast habs'

/-- Reduced rational endpoint denominators never exceed the common grid denominator. -/
theorem grid_endpoint_heights (a : ℝ) {Q R : ℕ} (hQ : 0 < Q) (ha : |a| ≤ R) :
    rationalHeight (gridLower a Q) ≤ Q * (R + 1) + 3 ∧
      rationalHeight (gridUpper a Q) ≤ Q * (R + 1) + 3 := by
  have hfloor := floor_grid_natAbs_le a Q R ha
  have hden : (Q : ℤ) ≠ 0 := by exact_mod_cast hQ.ne'
  have loNum := divInt_num_le (⌊(Q : ℝ) * a⌋ - 1) Q hden
  have hiNum := divInt_num_le (⌊(Q : ℝ) * a⌋ + 2) Q hden
  have loDen := divInt_den_le (⌊(Q : ℝ) * a⌋ - 1) Q hden
  have hiDen := divInt_den_le (⌊(Q : ℝ) * a⌋ + 2) Q hden
  rw [Rat.divInt_eq_div] at loNum hiNum loDen hiDen
  simp only [Int.cast_natCast, Int.natAbs_natCast] at loNum hiNum loDen hiDen
  have hlo : (⌊(Q : ℝ) * a⌋ - 1 : ℤ).natAbs ≤ Q * R + 2 := by
    have h := Int.natAbs_sub_le (⌊(Q : ℝ) * a⌋) 1
    simp only [Int.natAbs_one] at h
    omega
  have hhi : (⌊(Q : ℝ) * a⌋ + 2 : ℤ).natAbs ≤ Q * R + 3 := by
    have h := Int.natAbs_add_le (⌊(Q : ℝ) * a⌋) 2
    norm_num at h
    omega
  have hbase : Q * R ≤ Q * (R + 1) := Nat.mul_le_mul_left Q (Nat.le_succ R)
  have hQR : Q ≤ Q * (R + 1) := Nat.le_mul_of_pos_right Q (Nat.succ_pos R)
  exact ⟨max_le (loNum.trans (by omega)) (loDen.trans (by omega)),
    max_le (hiNum.trans (by omega)) (hiDen.trans (by omega))⟩

end Paper2.ExactInput
