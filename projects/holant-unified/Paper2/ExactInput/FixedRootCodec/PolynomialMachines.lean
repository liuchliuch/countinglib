import Paper2.ExactInput.FixedRootCodec.Signs
import Paper2.ExactInput.FixedRootCodec.Combinators
import Paper2.ExactInput.RootCode
import Paper2.Complexity.BellMachines.FieldArithmetic

/-! Exact evaluation and sign of a fixed rational polynomial by finite bit
programs. Polynomial degrees and coefficients become fixed program constants.
The runtime input remains an arbitrary canonical rational number. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines
noncomputable section

def rationalPowerComputes : (k : ℕ) →
    Computes rationalEncoding rationalEncoding (fun q : ℚ => q ^ k)
  | 0 => congrComputes (constantComputes rationalEncoding rationalEncoding 1)
      (fun _ => (pow_zero _).symm)
  | k + 1 => congrComputes
      (rationalProvider.mulComputes (rationalPowerComputes k) (identityComputes rationalEncoding))
      (fun q => (pow_succ q k).symm)

def polynomialComputes : (p : RationalPolynomialCode) →
    Computes rationalEncoding rationalEncoding (fun q => RationalPolynomialCode.evalRational q p)
  | [] => constantComputes rationalEncoding rationalEncoding 0
  | (k,a) :: p => rationalProvider.addComputes
      (rationalProvider.mulComputes (constantComputes rationalEncoding rationalEncoding a)
        (rationalPowerComputes k)) (polynomialComputes p)

def polynomialNegativeComputes (p : RationalPolynomialCode) :
    Computes rationalEncoding encodingBoolBool
      (fun q => decide (RationalPolynomialCode.evalRational q p < 0)) :=
  congrComputes ((polynomialComputes p).andThen rationalNegativeComputes) (fun _ => rfl)

def polynomialZeroComputes (p : RationalPolynomialCode) :
    Computes rationalEncoding encodingBoolBool
      (fun q => decide (RationalPolynomialCode.evalRational q p = 0)) :=
  congrComputes ((polynomialComputes p).andThen (zeroComputes rationalEncoding)) (fun _ => rfl)

end
end Paper2.ExactInput.FixedRootCodec
