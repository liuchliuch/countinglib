import ComplexCSP.Algebra.EncodedNumberFieldPresentation
import ComplexCSP.Algebra.EncodedNumberFieldCheckedOracle
import ComplexCSP.Recognition.GlobalCorrectness

/-! # Exact recognition: checked raw-coordinate global BO algorithm

The runtime input is a monic integer tail and finite rational-coordinate tables.
The finite guard derives the field laws; the trace-box algorithm supplies the
actual root alphabet. No Model, root enumeration, identity oracle or complex
embedding is a runtime input. Embeddings occur only in the correctness theorem.
Conversion from arbitrary complex algebraic-number encodings remains separate.
-/
namespace ComplexCSP.Recognition
open EncodedNumberField EffectiveRoots

variable {n : ℕ} (a : Fin n → ℤ)
variable {D ι : Type} [Fintype D] [DecidableEq D] [Encodable D] [Fintype ι]

/-- The finite program on already validated raw data. All semantic evidence is
erased; arithmetic, root enumeration and certificate loops use explicit code. -/
def coordinateGlobalTest (ha : validTail a = true)
    (L : Language D (Element n (coefficientRelation a)) ι) : Bool := by
  letI : Fact (Element.Valid n (coefficientRelation a)) := ⟨validTail_sound a ha⟩
  let hp := Element.integralPresentation_of_checkedTail a ha
  let α := Element.generator (c := coefficientRelation a)
  letI := runtimeRootFintype a α hp
  letI := runtimeRootEncodable a α hp
  letI := Element.unbarredStarRing (n := n) (c := coefficientRelation a)
  exact globalCertificateTest L (runtimeRootAlphabet a)

/-- Public guarded entry point. Invalid or degree-zero polynomial input returns
none; valid input returns the computed BO decision. -/
def checkedCoordinateGlobalTest
    (L : Language D (Element n (coefficientRelation a)) ι) : Option Bool :=
  if ha : validTail a = true then some (coordinateGlobalTest a ha L) else none

/-- The algorithm decides actual joint legal BO of the full embedded generated
family. The auxiliary identity involution is safe because the certificate-program
coordinates are unbarred; the generic correctness theorem already proves this. -/
theorem coordinateGlobalTest_correct [Nonempty D] (ha : validTail a = true)
    (L : Language D (Element n (coefficientRelation a)) ι) :
    letI : Fact (Element.Valid n (coefficientRelation a)) := ⟨validTail_sound a ha⟩
    ∀ σ : Element n (coefficientRelation a) →+* ℂ,
      coordinateGlobalTest a ha L = true ↔ JointBO (L.mapValues σ) := by
  letI : Fact (Element.Valid n (coefficientRelation a)) := ⟨validTail_sound a ha⟩
  let hp := Element.integralPresentation_of_checkedTail a ha
  let α := Element.generator (c := coefficientRelation a)
  letI := runtimeRootFintype a α hp
  letI := runtimeRootEncodable a α hp
  letI := Element.unbarredStarRing (n := n) (c := coefficientRelation a)
  intro σ
  exact globalCertificateTest_exponent_correct_jointBO
    (rootExponentFromCoefficients n a)
    (lt_of_lt_of_le (by decide) (presentation_rootExponent_ge_two hp))
    (presentation_rootExponent_killsTorsion hp) L σ

theorem checkedCoordinateGlobalTest_correct [Nonempty D] (ha : validTail a = true)
    (L : Language D (Element n (coefficientRelation a)) ι) :
    letI : Fact (Element.Valid n (coefficientRelation a)) := ⟨validTail_sound a ha⟩
    ∀ σ : Element n (coefficientRelation a) →+* ℂ,
      checkedCoordinateGlobalTest a L = some true ↔ JointBO (L.mapValues σ) := by
  letI : Fact (Element.Valid n (coefficientRelation a)) := ⟨validTail_sound a ha⟩
  intro σ
  simpa only [checkedCoordinateGlobalTest, dif_pos ha, Option.some.injEq] using
    coordinateGlobalTest_correct a ha L σ

/-- The same raw algorithm decides all three structural tractability conditions
for the exact embedded language. This uses the corrected all-instance isomorphism theorem. -/
theorem checkedCoordinateGlobalTest_correct_conditions [Nonempty D] (ha : validTail a = true)
    (L : Language D (Element n (coefficientRelation a)) ι) :
    letI : Fact (Element.Valid n (coefficientRelation a)) := ⟨validTail_sound a ha⟩
    ∀ σ : Element n (coefficientRelation a) →+* ℂ,
      checkedCoordinateGlobalTest a L = some true ↔ CaiChenConditions (L.mapValues σ) := by
  letI : Fact (Element.Valid n (coefficientRelation a)) := ⟨validTail_sound a ha⟩
  intro σ
  exact (checkedCoordinateGlobalTest_correct a ha L σ).trans
    (structural_collapse (L.mapValues σ) (mapped_language_algebraic L σ)).symm

@[simp] theorem checkedCoordinateGlobalTest_invalid (ha : validTail a = false)
    (L : Language D (Element n (coefficientRelation a)) ι) :
    checkedCoordinateGlobalTest a L = none := by simp [checkedCoordinateGlobalTest, ha]

end ComplexCSP.Recognition
