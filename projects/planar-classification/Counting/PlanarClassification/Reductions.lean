import PlanarHom.OracleReductionLaws
import PlanarHom.AlgebraPolynomialInterpolation

/-! Machine-level promised reduction laws and scalar-field interpolation tools. -/
namespace Counting.PlanarClassification
open PlanarHom.Complexity

/-- The concrete one-query identity reduction, valid for every extending oracle. -/
noncomputable def promiseReflexivity (P : PromiseProblem) (p : Polynomial ℕ)
    (outputBound : ∀ x, P.valid x → (P.value x).length ≤ p.eval x.length) :
    PromisePolyTimeTuringReduction P P :=
  PromisePolyTimeTuringReduction.refl_of_output_bound P p outputBound

/-- Exercise real oracle-machine composition and elimination on bit strings. -/
theorem identity_compiler : FP BitEncoding.bits BitEncoding.bits id :=
  identity_compiler_regression

end Counting.PlanarClassification
