import Paper2.ReedMullerNormalization.Endpoint
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace Paper2.ReedMullerNormalization

/-- Existence remains within the manuscript's actual algebraic-complex field. -/
theorem exists_algebraic_normalizing_root (A c : Tractable.AlgebraicComplex)
    (hA : A ≠ 0) (hc : c ≠ 0) :
    ∃ s : Tractable.AlgebraicComplex, s ≠ 0 ∧ s ^ 8 = c / A :=
  @exists_normalizing_root Tractable.AlgebraicComplex _
    (IsAlgClosure.isAlgClosed ℚ) A c hA hc


end Paper2.ReedMullerNormalization
