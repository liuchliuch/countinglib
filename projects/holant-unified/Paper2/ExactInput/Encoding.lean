import Paper2.ExactInput.RootCode
import Paper2.Complexity.FramedEncoding

/-! Executable faithful byte codecs for literal rational root descriptors.
Parsing raw syntax does not purport to decide root isolation or irreducibility. -/
namespace Paper2.ExactInput
open Computability Paper2.Complexity Paper2.Algebraic

/-- Sparse polynomial terms retain every exponent and rational coefficient. -/
def polynomialEncoding : Encoding RationalPolynomialCode Bool :=
  framedListEncoding (framedProductEncoding encodingNatBool rationalEncoding)

private def fourRationalEncoding : Encoding (ℚ × ℚ × ℚ × ℚ) Bool :=
  framedProductEncoding rationalEncoding (framedProductEncoding rationalEncoding
    (framedProductEncoding rationalEncoding rationalEncoding))

def rectangleEncoding : Encoding RationalRectangle Bool where
  encode r := fourRationalEncoding.encode (r.reLower, r.reUpper, r.imLower, r.imUpper)
  decode bits := (fourRationalEncoding.decode bits).map (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩)
  decode_encode r := by simp

def rootEncoding : Encoding RootCode Bool where
  encode c := (framedProductEncoding polynomialEncoding rectangleEncoding).encode
    (c.coefficients, c.rectangle)
  decode bits := ((framedProductEncoding polynomialEncoding rectangleEncoding).decode bits).map
    (fun p => ⟨p.1, p.2⟩)
  decode_encode c := by simp

theorem rootEncoding_injective : Function.Injective rootEncoding.encode :=
  rootEncoding.encode_injective

end Paper2.ExactInput
