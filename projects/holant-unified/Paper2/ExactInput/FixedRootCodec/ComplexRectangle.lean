import Paper2.ExactInput.FixedRootCodec.LinearApproximation
import Paper2.ExactInput.FixedRootCodec.ComplexAlgebraicity
import Paper2.ExactInput.Encoding
import Mathlib.Analysis.Complex.Norm

/-! Polynomial finite circuits output literal rational rectangles around a
variable rational linear combination of a fixed algebraic complex basis.
Both real and imaginary sides are strictly open, including the zero answer. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open scoped BigOperators
noncomputable section
variable {n : ℕ}

structure ComplexBrackets (z : Fin n → ℂ) where
  real : ∀ i, RealBracket (z i).re
  imag : ∀ i, RealBracket (z i).im

def complexBrackets (z : Fin n → ℂ) (hz : ∀ i, IsAlgebraic ℚ (z i)) : ComplexBrackets z where
  real i := Classical.choice (realBracket_exists _ (algebraic_re (z i) (hz i)))
  imag i := Classical.choice (realBracket_exists _ (algebraic_im (z i) (hz i)))

def complexLinearValue (z : Fin n → ℂ) (v : Fin n → ℚ) : ℂ := ∑ i, (v i : ℂ) * z i

theorem complexLinearValue_re (z : Fin n → ℂ) (v : Fin n → ℚ) :
    (complexLinearValue z v).re = ∑ i, (v i : ℝ) * (z i).re := by
  simp [complexLinearValue,Complex.mul_re]

theorem complexLinearValue_im (z : Fin n → ℂ) (v : Fin n → ℚ) :
    (complexLinearValue z v).im = ∑ i, (v i : ℝ) * (z i).im := by
  simp [complexLinearValue,Complex.mul_im]

def complexRectangle {z : Fin n → ℂ} (b : ComplexBrackets z) (k : ℕ) (v : Fin n → ℚ) :
    RationalRectangle :=
  ⟨(realLinearApproximation b.real k v).1,(realLinearApproximation b.real k v).2,
    (realLinearApproximation b.imag k v).1,(realLinearApproximation b.imag k v).2⟩

def complexRectangleComputes {z : Fin n → ℂ} (b : ComplexBrackets z) :
    Computes (precisionVectorEncoding n) rectangleEncoding
      (fun x => complexRectangle b x.1 x.2) := by
  let r := realLinearApproximationComputes b.real
  let i := realLinearApproximationComputes b.imag
  let rl := r.andThen (Wiring.firstComputes rationalEncoding rationalEncoding)
  let ru := r.andThen (Wiring.secondComputes rationalEncoding rationalEncoding)
  let il := i.andThen (Wiring.firstComputes rationalEncoding rationalEncoding)
  let iu := i.andThen (Wiring.secondComputes rationalEncoding rationalEncoding)
  exact recode (pairComputes rl (pairComputes ru (pairComputes il iu))) id
    (fun _ => rfl) (fun _ => rfl)

theorem complexRectangle_contains {z : Fin n → ℂ} (b : ComplexBrackets z)
    (k : ℕ) (v : Fin n → ℚ) : (complexRectangle b k v).Contains (complexLinearValue z v) := by
  have hr := realLinearApproximation_contains b.real k v
  have hi := realLinearApproximation_contains b.imag k v
  change _ < (complexLinearValue z v).re ∧ (complexLinearValue z v).re < _ ∧
    _ < (complexLinearValue z v).im ∧ (complexLinearValue z v).im < _
  rw [complexLinearValue_re,complexLinearValue_im]
  exact ⟨hr.1,hr.2,hi.1,hi.2⟩

theorem complexRectangle_width_bound {z : Fin n → ℂ} (b : ComplexBrackets z) :
    ∃ D : ℕ, ∀ (k B : ℕ) (v : Fin n → ℚ), (∀ i, rationalBitHeight (v i) ≤ B) →
      (complexRectangle b k v).reUpper - (complexRectangle b k v).reLower ≤
        (2 : ℚ)^(B+D) / 2^k ∧
      (complexRectangle b k v).imUpper - (complexRectangle b k v).imLower ≤
        (2 : ℚ)^(B+D) / 2^k := by
  obtain ⟨Dr,hr⟩ := bracketWidth_power_bound b.real
  obtain ⟨Di,hi⟩ := bracketWidth_power_bound b.imag
  refine ⟨max Dr Di,fun k B v hv => ?_⟩
  have hr' : (∑ i, bracketWidth (b.real i)) + 2 ≤ (2 : ℚ)^(max Dr Di) :=
    hr.trans (pow_le_pow_right₀ (by norm_num) (le_max_left Dr Di))
  have hi' : (∑ i, bracketWidth (b.imag i)) + 2 ≤ (2 : ℚ)^(max Dr Di) :=
    hi.trans (pow_le_pow_right₀ (by norm_num) (le_max_right Dr Di))
  have width (a : Fin n → ℝ) (bs : ∀ i, RealBracket (a i))
      (h : (∑ i, bracketWidth (bs i)) + 2 ≤ (2 : ℚ)^(max Dr Di)) :
      (realLinearApproximation bs k v).2 - (realLinearApproximation bs k v).1 ≤
        (2 : ℚ)^(B + max Dr Di)/2^k := by
    apply (realLinearApproximation_width bs k B v hv).trans
    rw [pow_add]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (by positivity))
      (by positivity)
  exact ⟨width _ b.real hr',width _ b.imag hi'⟩

theorem rectangle_near {r : RationalRectangle} {z w : ℂ} (hz : r.Contains z) (hw : r.Contains w) :
    ‖w-z‖ < (r.reUpper : ℝ) - r.reLower + ((r.imUpper : ℝ) - r.imLower) := by
  have hre : |w.re-z.re| < (r.reUpper : ℝ) - r.reLower :=
    abs_lt.mpr ⟨by linarith [hw.1,hz.2.1],by linarith [hw.2.1,hz.1]⟩
  have him : |w.im-z.im| < (r.imUpper : ℝ) - r.imLower :=
    abs_lt.mpr ⟨by linarith [hw.2.2.1,hz.2.2.2],by linarith [hw.2.2.2,hz.2.2.1]⟩
  have hn := Complex.norm_le_abs_re_add_abs_im (w-z)
  simp only [Complex.sub_re,Complex.sub_im] at hn
  exact hn.trans_lt (add_lt_add hre him)

end
end Paper2.ExactInput.FixedRootCodec
