import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Rat

/-! # Executable Gaussian rational arithmetic and rigorous norm bounds -/

namespace ComplexCSP

/-- Exact complex rational pairs, with executable inherited ring arithmetic. -/
abbrev GaussianRational := QuadraticAlgebra ℚ (-1) 0

namespace GaussianRational

instance : Encodable GaussianRational :=
  Encodable.ofEquiv (ℚ × ℚ) (QuadraticAlgebra.equivProd (-1) 0)

/-- The semantic complex embedding. It is never used by runtime checks. -/
noncomputable def toComplex : GaussianRational →+* ℂ where
  toFun z := ⟨z.re, z.im⟩
  map_zero' := by apply Complex.ext <;> simp
  map_one' := by apply Complex.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' z w := by apply Complex.ext <;> simp
  map_mul' z w := by apply Complex.ext <;> simp; ring

@[simp] theorem toComplex_re (z : GaussianRational) : (toComplex z).re = z.re := rfl
@[simp] theorem toComplex_im (z : GaussianRational) : (toComplex z).im = z.im := rfl

theorem toComplex_injective : Function.Injective toComplex := by
  intro z w h
  apply QuadraticAlgebra.ext
  · exact_mod_cast (show (z.re : ℝ) = w.re from congrArg Complex.re h)
  · exact_mod_cast (show (z.im : ℝ) = w.im from congrArg Complex.im h)

/-- Rational upper bound for Euclidean norm. -/
def upper (z : GaussianRational) : ℚ := |z.re| + |z.im|

/-- Rational lower bound for Euclidean norm. -/
def lower (z : GaussianRational) : ℚ := max |z.re| |z.im|

theorem upper_nonneg (z : GaussianRational) : 0 ≤ upper z := by
  unfold upper; positivity

theorem lower_nonneg (z : GaussianRational) : 0 ≤ lower z :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem norm_le_upper (z : GaussianRational) : ‖toComplex z‖ ≤ (upper z : ℝ) := by
  simpa [upper] using Complex.norm_le_abs_re_add_abs_im (toComplex z)

theorem lower_le_norm (z : GaussianRational) : (lower z : ℝ) ≤ ‖toComplex z‖ := by
  simpa [lower] using max_le (Complex.abs_re_le_norm (toComplex z))
    (Complex.abs_im_le_norm (toComplex z))

/-- Rational centers are dense in the complex plane, with an explicit norm
accuracy statement useful in strict-certificate completeness proofs. -/
theorem exists_near (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : GaussianRational, ‖toComplex c - z‖ < ε := by
  obtain ⟨a,ha₁,ha₂⟩ := exists_rat_btwn (show z.re - ε/2 < z.re + ε/2 by linarith)
  obtain ⟨b,hb₁,hb₂⟩ := exists_rat_btwn (show z.im - ε/2 < z.im + ε/2 by linarith)
  refine ⟨⟨a,b⟩, ?_⟩
  apply lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _)
  have ha : |(a : ℝ) - z.re| < ε/2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hb : |(b : ℝ) - z.im| < ε/2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  change |(a : ℝ) - z.re| + |(b : ℝ) - z.im| < ε
  linarith

end GaussianRational
end ComplexCSP
