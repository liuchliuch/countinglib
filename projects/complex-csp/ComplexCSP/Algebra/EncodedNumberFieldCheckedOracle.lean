import ComplexCSP.Algebra.EncodedNumberFieldValidation
import ComplexCSP.Recognition.IdentityOracle

/-! # Guarded raw-data oracle for unbarred polynomial identities

The monic integer tail is checked by a finite irreducibility test before a field
dictionary is installed. No model or field-operation oracle is an input.
The separately named identity involution is used only for direct coordinates:
the resulting specification contains no conjugation. General star identities
continue to use the genuine complex-conjugation interface in EncodedNumberFieldOracle.
-/
namespace ComplexCSP.EncodedNumberField

namespace Element
variable {n : ℕ} {c : CoeffVector n} [Fact (Valid n c)]

/-- An explicitly labelled auxiliary involution for algorithms restricted to
unbarred coordinates. It makes no claim to represent complex conjugation. -/
def unbarredStarRing : StarRing (Element n c) where
  star := id
  star_involutive _ := rfl
  star_mul := mul_comm
  star_add _ _ := rfl
end Element

variable {n : ℕ} (a : Fin n → ℤ)
variable {D ι V : Type} [Fintype D] [DecidableEq D] [Fintype ι] [Fintype V] {r : ℕ}

/-- Raw integer/rational-data ingress to the repaired identity algorithm.
`none` means that the input relation failed finite validation. -/
def checkedUnbarredIdentityTest
    (L : Language D (Element n (EffectiveRoots.coefficientRelation a)) ι)
    (coords : Fin r → (V → D))
    (P : PolynomialPrograms.Program (Element n (EffectiveRoots.coefficientRelation a)) r) :
    Option Bool :=
  if h : validTail a = true then
    letI : Fact (Element.Valid n (EffectiveRoots.coefficientRelation a)) := ⟨validTail_sound a h⟩
    letI := Element.unbarredStarRing (n := n) (c := EffectiveRoots.coefficientRelation a)
    some (Recognition.programIdentityTest L (fun i => Sum.inl (coords i)) P)
  else none

/-- Exact universal unbarred semantics after a successful finite guard. All
model-existence evidence is supplied by the checked raw input itself. -/
theorem checkedUnbarredIdentityTest_correct
    (L : Language D (Element n (EffectiveRoots.coefficientRelation a)) ι)
    (coords : Fin r → (V → D))
    (P : PolynomialPrograms.Program (Element n (EffectiveRoots.coefficientRelation a)) r)
    (ha : validTail a = true) :
    letI : Fact (Element.Valid n (EffectiveRoots.coefficientRelation a)) := ⟨validTail_sound a ha⟩
    checkedUnbarredIdentityTest a L coords P = some true ↔
      ∀ Q : Presentation L V, PolynomialPrograms.eval (fun j => Q.table (coords j)) P = 0 := by
  letI : Fact (Element.Valid n (EffectiveRoots.coefficientRelation a)) := ⟨validTail_sound a ha⟩
  letI := Element.unbarredStarRing (n := n) (c := EffectiveRoots.coefficientRelation a)
  simp only [checkedUnbarredIdentityTest, dif_pos ha, Option.some.injEq]
  exact Recognition.programIdentityTest_correct L (fun i => Sum.inl (coords i)) P

@[simp] theorem checkedUnbarredIdentityTest_invalid
    (L : Language D (Element n (EffectiveRoots.coefficientRelation a)) ι)
    (coords : Fin r → (V → D))
    (P : PolynomialPrograms.Program (Element n (EffectiveRoots.coefficientRelation a)) r)
    (ha : validTail a = false) : checkedUnbarredIdentityTest a L coords P = none := by
  simp [checkedUnbarredIdentityTest, ha]

end ComplexCSP.EncodedNumberField
