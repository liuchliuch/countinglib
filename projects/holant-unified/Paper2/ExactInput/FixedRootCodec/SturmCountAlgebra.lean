import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Basic.Sign.Basic

/-! Finite algebra behind Sturm counting. The integer formula uses the values
`-1,0,1` of the signs. Internal zero entries contribute two half-edges; opposite
neighbors make their sum one full variation. A zero first entry uses the right
limit, because the second entry is the derivative. -/
namespace Paper2.ExactInput.FixedRootCodec.SturmCount
open scoped BigOperators
open Filter Topology Polynomial SignType
noncomputable section

/-- The sign, represented as an integer suitable for exact finite arithmetic. -/
def integerSign (x : ℝ) : ℤ := SignType.cast (sign x)

@[simp] theorem integerSign_zero : integerSign 0 = 0 := by simp [integerSign]
@[simp] theorem integerSign_neg (x : ℝ) : integerSign (-x) = -integerSign x := by
  simp [integerSign, Left.sign_neg]

theorem integerSign_eq_zero_iff (x : ℝ) : integerSign x = 0 ↔ x = 0 := by
  unfold integerSign
  have : (SignType.cast (sign x) : ℤ) = 0 ↔ sign x = 0 := by
    cases sign x <;> decide
  exact this.trans sign_eq_zero_iff

theorem integerSign_sq {x : ℝ} (hx : x ≠ 0) : integerSign x * integerSign x = 1 := by
  rcases hx.lt_or_gt with h | h
  · simp [integerSign, sign_neg h]
  · simp [integerSign, sign_pos h]

/-- Expansion of adjacent bilinear terms into the contributions of vertices. -/
theorem adjacent_bilinear_sum (n : ℕ) (s δ : ℕ → ℤ) :
    (∑ i ∈ Finset.range (n + 1), (δ i * s (i+1) + s i * δ (i+1))) =
      δ 0 * s 1 + (∑ i ∈ Finset.range n, δ (i+1) * (s i + s (i+2))) +
        s n * δ (n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- Changing only zero entries of a Sturm sign vector changes its adjacent
product sum solely at the first entry. No adjacent zero is allowed, and every
internal zero has opposite neighbors. -/
theorem adjacent_product_change (n : ℕ) (s t : ℕ → ℤ)
    (hfixed : ∀ i ≤ n+1, s i ≠ 0 → t i = s i)
    (hlast : s (n+1) ≠ 0)
    (hadj : ∀ i < n+1, s i = 0 → s (i+1) ≠ 0)
    (hopp : ∀ i < n, s (i+1) = 0 → s i + s (i+2) = 0) :
    (∑ i ∈ Finset.range (n+1), t i * t (i+1)) -
      (∑ i ∈ Finset.range (n+1), s i * s (i+1)) = (t 0-s 0)*s 1 := by
  let δ : ℕ → ℤ := fun i => t i-s i
  have hcross : ∀ i ∈ Finset.range (n+1), δ i * δ (i+1) = 0 := by
    intro i hi
    have hi' : i < n+1 := Finset.mem_range.mp hi
    by_cases hz : s i = 0
    · have ht := hfixed (i+1) (by omega) (hadj i hi' hz)
      simp [δ, ht]
    · have ht := hfixed i (by omega) hz
      simp [δ, ht]
  have hexpand : ∀ i ∈ Finset.range (n+1),
      t i*t (i+1)-s i*s (i+1) = δ i*s (i+1)+s i*δ (i+1) := by
    intro i hi
    have hc := hcross i hi
    dsimp [δ] at hc ⊢
    nlinarith
  have hint : ∑ i ∈ Finset.range n, δ (i+1)*(s i+s (i+2)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    by_cases hz : s (i+1) = 0
    · simp [hopp i hi' hz]
    · simp [δ, hfixed (i+1) (by omega) hz]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ i ∈ Finset.range (n+1), (δ i*s (i+1)+s i*δ (i+1)) :=
      Finset.sum_congr rfl hexpand
    _ = δ 0*s 1 := by
      rw [adjacent_bilinear_sum, hint]
      simp [δ, hfixed (n+1) le_rfl hlast]

/-- Local algebraic conditions of a finite Sturm chain. They are consequences
of a genuine negative Euclidean remainder chain ending in a nonzero constant.
No variation or root-count property is an assumption. -/
structure Chain where
  tailLength : ℕ
  polynomial : ℕ → ℝ[X]
  head_ne : polynomial 0 ≠ 0
  derivative : polynomial 1 = (polynomial 0).derivative
  last_ne : ∀ x : ℝ, (polynomial (tailLength+1)).eval x ≠ 0
  adjacent : ∀ i < tailLength+1, ∀ x : ℝ,
    (polynomial i).eval x = 0 → (polynomial (i+1)).eval x ≠ 0
  opposite : ∀ i < tailLength, ∀ x : ℝ,
    (polynomial (i+1)).eval x = 0 →
      (polynomial (i+2)).eval x = -(polynomial i).eval x

namespace Chain

def signs (C : Chain) (x : ℝ) (i : ℕ) : ℤ :=
  integerSign ((C.polynomial i).eval x)

/-- Twice the usual zero-skipping variation, with its right-limit value at a
root of the first polynomial. This is an exact integer computation. -/
def doubledVariation (C : Chain) (x : ℝ) : ℤ :=
  (∑ i ∈ Finset.range (C.tailLength+1), (1-C.signs x i*C.signs x (i+1))) -
    if (C.polynomial 0).eval x = 0 then 1 else 0

theorem signs_last_ne (C : Chain) (x : ℝ) : C.signs x (C.tailLength+1) ≠ 0 := by
  simpa [signs, integerSign_eq_zero_iff] using C.last_ne x

theorem signs_adjacent (C : Chain) (x : ℝ) (i : ℕ) (hi : i < C.tailLength+1)
    (hz : C.signs x i = 0) : C.signs x (i+1) ≠ 0 := by
  have hz' := (integerSign_eq_zero_iff _).mp hz
  simpa [signs, integerSign_eq_zero_iff] using C.adjacent i hi x hz'

theorem signs_opposite (C : Chain) (x : ℝ) (i : ℕ) (hi : i < C.tailLength)
    (hz : C.signs x (i+1) = 0) : C.signs x i+C.signs x (i+2) = 0 := by
  have hz' := (integerSign_eq_zero_iff _).mp hz
  simp [signs, C.opposite i hi x hz']

end Chain
end
end Paper2.ExactInput.FixedRootCodec.SturmCount
