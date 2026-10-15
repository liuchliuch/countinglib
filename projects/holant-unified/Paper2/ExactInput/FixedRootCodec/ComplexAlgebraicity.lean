import Paper2.Tractable.Scalars
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Algebra.Algebra.Tower

/-! Real and imaginary parts of fixed algebraic complex constants are algebraic.
This supplies the fixed real bisection data used by the output codec. -/
namespace Paper2.ExactInput.FixedRootCodec
open Paper2.Tractable
noncomputable section

theorem algebraic_re (z : ℂ) (hz : IsAlgebraic ℚ z) : IsAlgebraic ℚ z.re := by
  let a : AlgebraicComplex := ⟨z,hz.isIntegral⟩
  let b : AlgebraicComplex := ⟨(starRingEnd ℂ) z,
    hz.isIntegral.map (AlgEquiv.restrictScalars ℚ Complex.conjAe).toAlgHom⟩
  have h : IsAlgebraic ℚ ((a + b) / 2 : AlgebraicComplex).val :=
    ((a + b) / 2 : AlgebraicComplex).property.isAlgebraic
  change IsAlgebraic ℚ ((z + (starRingEnd ℂ) z) / 2) at h
  rw [← Complex.re_eq_add_conj] at h
  exact (isAlgebraic_algebraMap_iff (R := ℚ) (A := ℂ) Complex.ofReal_injective).mp h

theorem algebraic_im (z : ℂ) (hz : IsAlgebraic ℚ z) : IsAlgebraic ℚ z.im := by
  let a : AlgebraicComplex := ⟨z,hz.isIntegral⟩
  let b : AlgebraicComplex := ⟨(starRingEnd ℂ) z,
    hz.isIntegral.map (AlgEquiv.restrictScalars ℚ Complex.conjAe).toAlgHom⟩
  have h : IsAlgebraic ℚ ((a - b) / (2 * imaginaryUnit) : AlgebraicComplex).val :=
    ((a - b) / (2 * imaginaryUnit) : AlgebraicComplex).property.isAlgebraic
  change IsAlgebraic ℚ ((z - (starRingEnd ℂ) z) / (2 * Complex.I)) at h
  rw [← Complex.im_eq_sub_conj] at h
  exact (isAlgebraic_algebraMap_iff (R := ℚ) (A := ℂ) Complex.ofReal_injective).mp h

end
end Paper2.ExactInput.FixedRootCodec
