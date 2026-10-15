import ComplexCSP.Algebra.AlgebraicInput
import ComplexCSP.Algebra.InitialPrimitiveCoordinates
import ComplexCSP.Algebra.ComplexRootCertificatesInput

/-! # Finite candidates for uniform conversion of separate algebraic inputs

A candidate contains only integer/rational data. It certifies a common monic
irreducible field, one selected complex root, coordinates for every given input,
and a polynomial expression for the primitive generator in those inputs.
No field model, equality oracle, or complex number is stored or evaluated.
-/
namespace ComplexCSP.AlgebraicEncoding
open EncodedNumberField ComplexRootCertificates PolynomialPrograms

/-- Literal finite certificate data for a common primitive presentation. -/
structure InitialInputCandidate (m : ℕ) where
  degree : ℕ
  tail : Fin degree → ℤ
  coordinates : Fin m → CoeffVector degree
  expression : Program ℚ m
  center : GaussianRational
  radius : ℚ

abbrev InitialCandidateData (m : ℕ) :=
  Σ n : ℕ, (Fin n → ℤ) × (Fin m → CoeffVector n) × Program ℚ m × GaussianRational × ℚ

def InitialInputCandidate.dataEquiv (m : ℕ) : InitialInputCandidate m ≃ InitialCandidateData m where
  toFun C := ⟨C.degree,C.tail,C.coordinates,C.expression,C.center,C.radius⟩
  invFun x := ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2.1,x.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {m : ℕ} : Encodable (InitialInputCandidate m) :=
  Encodable.ofEquiv (InitialCandidateData m) (InitialInputCandidate.dataEquiv m)

namespace InitialInputCandidate
variable {m : ℕ}

abbrev FieldType (C : InitialInputCandidate m) :=
  Element C.degree (EffectiveRoots.coefficientRelation C.tail)

def coordinateValue (C : InitialInputCandidate m) (i : Fin m) : C.FieldType :=
  ⟨C.coordinates i⟩

/-- Literal exact checks. The defining-polynomial guard proves all field laws;
its proof is erased, and every subsequent operation uses rational vectors. -/
def test (C : InitialInputCandidate m) (input : Fin m → AlgebraicInput) : Bool :=
  if h : validTail C.tail = true then
    letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
      ⟨validTail_sound C.tail h⟩
    rootCertificateMonicTail C.tail C.center C.radius &&
      decide ((∀ i, evalIntegerList (input i).coefficients (C.coordinateValue i) = 0 ∧
        imageCertificateRatVector (C.coordinates i) C.center C.radius (input i).rectangle = true) ∧
        PolynomialPrograms.interpret (algebraMap ℚ C.FieldType) C.coordinateValue C.expression =
          Element.generator)
  else false

 theorem test_valid {C : InitialInputCandidate m} {input : Fin m → AlgebraicInput}
    (h : C.test input = true) : validTail C.tail = true := by
  unfold test at h
  split_ifs at h with hv
  exact hv

 theorem test_spec (C : InitialInputCandidate m) (input : Fin m → AlgebraicInput)
    (hv : validTail C.tail = true) :
    letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
      ⟨validTail_sound C.tail hv⟩
    C.test input = true ↔
      rootCertificateMonicTail C.tail C.center C.radius = true ∧
      (∀ i, evalIntegerList (input i).coefficients (C.coordinateValue i) = 0 ∧
        imageCertificateRatVector (C.coordinates i) C.center C.radius (input i).rectangle = true) ∧
      PolynomialPrograms.interpret (algebraMap ℚ C.FieldType) C.coordinateValue C.expression =
        Element.generator := by
  simp [test, hv]

end InitialInputCandidate
end ComplexCSP.AlgebraicEncoding
