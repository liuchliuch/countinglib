import Paper2.ExactInput.DifferenceAnnihilator
import Paper2.ExactInput.NonzeroRootBound

/-! Polynomial-precision separation for all distinct conjugates of a fixed-field
coordinate value. The constant is derived from the original fixed field; it is
not an additional separation hypothesis. -/
namespace Paper2.ExactInput
open Paper2.Algebraic Polynomial

/-- One fixed constant controls every pair of distinct minimal-polynomial roots
of every value whose rational coordinates have B-bit height. -/
theorem fixed_field_root_separation {K : Type*} [Field K] [Algebra ℚ K]
    {n : ℕ} (F : FixedField K n) :
    ∃ C : ℕ, ∀ (B : ℕ) (v : Fin n → ℚ), (∀ i, rationalBitHeight (v i) ≤ B) →
      ∀ z w : ℂ, Polynomial.aeval z (minpoly ℚ (F.decode v)) = 0 →
        Polynomial.aeval w (minpoly ℚ (F.decode v)) = 0 → w ≠ z →
        6 / ((6 * 2 ^ (2 * (C * (B + 1)) + 1) : ℕ) : ℝ) ≤ ‖w - z‖ := by
  obtain ⟨C, hC⟩ := differenceAnnihilator_height_bound F
  refine ⟨C, fun B v hv z w hz hw hne => ?_⟩
  have h := nonzero_root_norm_lower (differenceAnnihilator_monic F v).ne_zero
    (hC B v hv) (sub_ne_zero.mpr hne) (differenceAnnihilator_roots F v hw hz)
  push_cast
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 6 * 2 ^ (2 * (C * (B + 1)) + 1))).mpr
  nlinarith

end Paper2.ExactInput
