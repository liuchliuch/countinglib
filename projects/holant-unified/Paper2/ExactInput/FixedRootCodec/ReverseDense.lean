import Paper2.ExactInput.FixedRootCodec.ReverseRational
import Paper2.ExactInput.FixedRootCodec.VariablePolynomial

/-! Fixed-degree dense input for variable polynomial circuits. Arbitrary
literal sparse coefficients are summed by their physical scanner before the
fixed vector is serialized. No sparse ordering or uniqueness promise is used. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines
noncomputable section

def denseCoefficients (n : ℕ) (p : RationalPolynomialCode) : Fin n → ℚ :=
  fun i => sparseCoefficient i.val p

def denseCoefficientsComputes (n : ℕ) :
    Computes polynomialEncoding (vectorEncoding n) (denseCoefficients n) :=
  assembleComputes polynomialEncoding n (denseCoefficients n)
    (fun i => sparseCoefficientComputes i.val)

theorem denseCoefficients_polynomial (n : ℕ) (p : RationalPolynomialCode)
    (h : p.polynomial.natDegree<n) :
    VariablePolynomial.polynomial (denseCoefficients n p)=p.polynomial := by
  simp only [VariablePolynomial.polynomial,denseCoefficients,sparseCoefficient_polynomial]
  rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i (p.polynomial.coeff i))]
  exact (p.polynomial.as_sum_range' n h).symm

def denseRootCoefficientsComputes (n : ℕ) :
    Computes rootEncoding (vectorEncoding n) (fun c => denseCoefficients n c.coefficients) :=
  rootCoefficientsComputes.andThen (denseCoefficientsComputes n)

theorem denseRootCoefficients_polynomial (n : ℕ) (c : RootCode)
    (h : c.polynomial.natDegree<n) :
    VariablePolynomial.polynomial (denseCoefficients n c.coefficients)=c.polynomial :=
  denseCoefficients_polynomial n c.coefficients h

def rootDenominatorComputes : Computes rootEncoding encodingNatBool
    (fun c => sparseDenominator c.coefficients) :=
  rootCoefficientsComputes.andThen sparseDenominatorComputes

end
end Paper2.ExactInput.FixedRootCodec
