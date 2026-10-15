import ComplexCSP.Algebra.EncodedNumberFieldGlobal
import ComplexCSP.Recognition.DegreeConditionsGlobalProgram
import ComplexCSP.Algebra.UniformCyclotomicExtensionRuntime

/-! # Exact recognition: checked degree-multiple global recognition

The algorithm validates the raw common-field tail, computes a cyclotomic
extension by a proved terminating search, transports the finite input tables,
enumerates the new field's roots, and runs the degree-filtered finite certificate
program. No primitive root, extension field, root list or identity oracle is
supplied by the caller. This module retains the common-field input boundary;
the separate uniform frontend supplies algebraic-description conversion.
-/
set_option maxHeartbeats 1000000

namespace ComplexCSP.Recognition
open EncodedNumberField EffectiveRoots AlgebraicEncoding

variable {n : ℕ} (a : Fin n → ℤ)
variable {D ι : Type} [Fintype D] [DecidableEq D] [Encodable D] [Fintype ι]

/-- Actual degree recognition on validated data, including a computed primitive
filter root in a computed extension field. -/
def coordinateDegreeGlobalTest (ha : validTail a = true) (δ : ℕ) (hδ : 0 < δ)
    (L : Language D (Element n (coefficientRelation a)) ι) : Bool := by
  let C := findCyclotomicCandidate a ha δ hδ
  have hC : C.test a δ = true := findCyclotomicCandidate_spec a ha δ hδ
  letI : Fact (Element.Valid n (coefficientRelation a)) := ⟨validTail_sound a ha⟩
  letI : Fact (Element.Valid C.dimension C.relation) := ⟨candidate_valid a δ C hC⟩
  letI : Fact (Element.Valid C.dimension (coefficientRelation C.tail)) :=
    ⟨candidate_valid a δ C hC⟩
  let ψ : Element n (coefficientRelation a) →+*
      Element C.dimension (coefficientRelation C.tail) := candidateEmbedding a ha δ hδ C hC
  let hp := Element.integralPresentation_of_checkedTail C.tail (of_decide_eq_true hC).2.2.1
  let α := Element.generator (c := coefficientRelation C.tail)
  letI := runtimeRootFintype C.tail α hp
  letI := runtimeRootEncodable C.tail α hp
  letI := Element.unbarredStarRing (n := C.dimension) (c := C.relation)
  letI := Element.unbarredStarRing (n := C.dimension) (c := coefficientRelation C.tail)
  exact degreeGlobalCertificateTest (L.mapValues ψ) δ (⟨C.root⟩ : Element C.dimension (coefficientRelation C.tail))
    (runtimeRootAlphabet C.tail)

/-- Guarded raw-data entry point. Invalid relation input and degree modulus zero
are rejected before the extension search or certificate program. -/
def checkedCoordinateDegreeGlobalTest (δ : ℕ)
    (L : Language D (Element n (coefficientRelation a)) ι) : Option Bool :=
  if h : validTail a = true ∧ 0 < δ then some (coordinateDegreeGlobalTest a h.1 δ h.2 L)
  else none

/-- The computed extension is interpreted along an extension of any chosen old
complex embedding. The final condition is on the original input language. -/
theorem coordinateDegreeGlobalTest_correct [Nonempty D]
    (ha : validTail a = true) (δ : ℕ) (hδ : 0 < δ)
    (L : Language D (Element n (coefficientRelation a)) ι) :
    letI : Fact (Element.Valid n (coefficientRelation a)) := ⟨validTail_sound a ha⟩
    ∀ σ : Element n (coefficientRelation a) →+* ℂ,
      coordinateDegreeGlobalTest a ha δ hδ L = true ↔ DegreeJointBO (L.mapValues σ) δ := by
  let C := findCyclotomicCandidate a ha δ hδ
  have hC : C.test a δ = true := findCyclotomicCandidate_spec a ha δ hδ
  letI : Fact (Element.Valid n (coefficientRelation a)) := ⟨validTail_sound a ha⟩
  letI : Fact (Element.Valid C.dimension C.relation) := ⟨candidate_valid a δ C hC⟩
  letI : Fact (Element.Valid C.dimension (coefficientRelation C.tail)) :=
    ⟨candidate_valid a δ C hC⟩
  let ψ : Element n (coefficientRelation a) →+*
      Element C.dimension (coefficientRelation C.tail) := candidateEmbedding a ha δ hδ C hC
  let hp := Element.integralPresentation_of_checkedTail C.tail (of_decide_eq_true hC).2.2.1
  let α := Element.generator (c := coefficientRelation C.tail)
  letI := runtimeRootFintype C.tail α hp
  letI := runtimeRootEncodable C.tail α hp
  letI := Element.unbarredStarRing (n := C.dimension) (c := C.relation)
  letI := Element.unbarredStarRing (n := C.dimension) (c := coefficientRelation C.tail)
  intro σ
  obtain ⟨Φ,hΦ⟩ := exists_complex_embedding_extension ψ σ
  have hroot : IsPrimitiveRoot (⟨C.root⟩ : Element C.dimension (coefficientRelation C.tail)) δ :=
    (acceptedCandidate_equations a δ hδ C hC).2.1
  have ht : coordinateDegreeGlobalTest a ha δ hδ L = true ↔
      DegreeJointBO ((L.mapValues ψ).mapValues Φ) δ :=
    degreeGlobalCertificateTest_exponent_correct_jointBO
      (rootExponentFromCoefficients C.dimension C.tail)
      (lt_of_lt_of_le (by decide) (presentation_rootExponent_ge_two hp))
      (presentation_rootExponent_killsTorsion hp) (L.mapValues ψ) hδ hroot Φ
  simpa only [Language.mapValues_comp,hΦ] using ht

theorem checkedCoordinateDegreeGlobalTest_correct [Nonempty D]
    (ha : validTail a = true) (δ : ℕ) (hδ : 0 < δ)
    (L : Language D (Element n (coefficientRelation a)) ι) :
    letI : Fact (Element.Valid n (coefficientRelation a)) := ⟨validTail_sound a ha⟩
    ∀ σ : Element n (coefficientRelation a) →+* ℂ,
      checkedCoordinateDegreeGlobalTest a δ L = some true ↔ DegreeJointBO (L.mapValues σ) δ := by
  letI : Fact (Element.Valid n (coefficientRelation a)) := ⟨validTail_sound a ha⟩
  intro σ
  simpa only [checkedCoordinateDegreeGlobalTest, ha, hδ, and_self, ↓reduceDIte,
    Option.some.injEq] using coordinateDegreeGlobalTest_correct a ha δ hδ L σ

/-- Complete three-condition correctness at the explicitly stated common-field
input boundary, independent of the refuted original Theorem 5.2. -/
theorem checkedCoordinateDegreeGlobalTest_correct_conditions [Nonempty D]
    (ha : validTail a = true) (δ : ℕ) (hδ : 0 < δ)
    (L : Language D (Element n (coefficientRelation a)) ι) :
    letI : Fact (Element.Valid n (coefficientRelation a)) := ⟨validTail_sound a ha⟩
    ∀ σ : Element n (coefficientRelation a) →+* ℂ,
      checkedCoordinateDegreeGlobalTest a δ L = some true ↔ DegreeCaiChenConditions (L.mapValues σ) δ := by
  letI : Fact (Element.Valid n (coefficientRelation a)) := ⟨validTail_sound a ha⟩
  intro σ
  exact (checkedCoordinateDegreeGlobalTest_correct a ha δ hδ L σ).trans
    (degree_structural_collapse (L.mapValues σ) δ (mapped_language_algebraic L σ)).symm

@[simp] theorem checkedCoordinateDegreeGlobalTest_zero
    (L : Language D (Element n (coefficientRelation a)) ι) :
    checkedCoordinateDegreeGlobalTest a 0 L = none := by simp [checkedCoordinateDegreeGlobalTest]

@[simp] theorem checkedCoordinateDegreeGlobalTest_invalid (ha : validTail a = false) (δ : ℕ)
    (L : Language D (Element n (coefficientRelation a)) ι) :
    checkedCoordinateDegreeGlobalTest a δ L = none := by simp [checkedCoordinateDegreeGlobalTest,ha]

end ComplexCSP.Recognition
