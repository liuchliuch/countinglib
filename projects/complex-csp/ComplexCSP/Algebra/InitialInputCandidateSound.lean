import ComplexCSP.Algebra.InitialInputCandidate
import ComplexCSP.Algebra.RawTailComplexEmbedding

/-! # Soundness of common-field conversion candidates

The literal candidate tests identify the exact supplied complex values. The
selected root is proved to exist by rational disk certification; no complex
root finder or equality operation is part of the runtime candidate test.
-/
set_option backward.isDefEq.respectTransparency false

namespace ComplexCSP.AlgebraicEncoding
open EncodedNumberField ComplexRootCertificates PolynomialPrograms
open scoped BigOperators

namespace InitialInputCandidate
variable {m : ℕ}

/-- Stored coordinates have their usual value under any genuine field embedding. -/
theorem map_coordinateValue (C : InitialInputCandidate m) (hv : validTail C.tail = true) :
    letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
      ⟨validTail_sound C.tail hv⟩
    ∀ (σ : C.FieldType →+* ℂ) (i : Fin m),
      σ (C.coordinateValue i) = EncodedNumberField.interpret (σ Element.generator) (C.coordinates i) := by
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail hv⟩
  intro σ i
  rw [← Element.map_interpret_complex, Element.interpret_generator]
  rfl

/-- The accepted image and polynomial equations identify each input exactly,
using only the standard isolating-rectangle semantic promise. -/
theorem sound_of_root_realization (C : InitialInputCandidate m)
    (input : Fin m → AlgebraicInput) (z : Fin m → ℂ)
    (hz : ∀ i, (input i).Represents (z i)) (h : C.test input = true)
    (hv : validTail C.tail = true) :
    letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
      ⟨validTail_sound C.tail hv⟩
    ∀ (σ : C.FieldType →+* ℂ),
      ‖σ Element.generator - GaussianRational.toComplex C.center‖ ≤ (C.radius : ℝ) →
      (∀ i, σ (C.coordinateValue i) = z i) ∧
      PolynomialPrograms.interpret (algebraMap ℚ ℂ) z C.expression = σ Element.generator := by
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail hv⟩
  intro σ hnear
  obtain ⟨_hroot,hcoordinates,hexpression⟩ := (C.test_spec input hv).mp h
  have hvalues (i : Fin m) : σ (C.coordinateValue i) = z i := by
    apply (hz i).2.2.2
    · rw [← map_evalIntegerList, (hcoordinates i).1, map_zero]
    · have hb := imageCertificate_sound (ofRatVector (C.coordinates i)) C.center C.radius
        (input i).rectangle (hcoordinates i).2 (σ Element.generator) hnear
      rw [eval_denote_ofRatVector] at hb
      rwa [C.map_coordinateValue hv σ i]
  refine ⟨hvalues, ?_⟩
  have he := congrArg σ hexpression
  rw [PolynomialPrograms.map_interpret] at he
  have hrat : σ.comp (algebraMap ℚ C.FieldType) = algebraMap ℚ ℂ := by
    ext q
    simp
  simpa only [hrat,hvalues] using he

/-- Acceptance constructs a genuine complex embedding and identifies every
input value. The embedding and complex root occur only in this proof. -/
theorem sound (C : InitialInputCandidate m) (input : Fin m → AlgebraicInput)
    (z : Fin m → ℂ) (hz : ∀ i, (input i).Represents (z i))
    (h : C.test input = true) :
    letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
      ⟨validTail_sound C.tail (test_valid h)⟩
    ∃ σ : C.FieldType →+* ℂ,
      (∀ i, σ (C.coordinateValue i) = z i) ∧
      PolynomialPrograms.interpret (algebraMap ℚ ℂ) z C.expression = σ Element.generator := by
  let hv := test_valid h
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail hv⟩
  have hcert := ((C.test_spec input hv).mp h).1
  obtain ⟨α,hα,_hunique⟩ := rootCertificate_sound (ofMonicIntTail C.tail) C.center C.radius hcert
  let p := RawTailComplexEmbedding.polynomial C.tail
  have hp : p.Monic := MonicIrreducibility.denote_monic _
    (MonicIrreducibility.fromTail_leading C.tail)
  have hd : p.natDegree = C.degree := MonicIrreducibility.denote_natDegree _
    (MonicIrreducibility.fromTail_leading C.tail)
  have hc (i : Fin C.degree) : p.coeff i.val = C.tail i := by
    simp [p, RawTailComplexEmbedding.polynomial, MonicIrreducibility.coefficient,
      MonicIrreducibility.fromTail, i.isLt, show i.val < C.degree+1 by omega]
  have hroot : Polynomial.aeval α p = 0 := by
    have he := hα.2
    rw [denote_ofMonicIntTail_eq C.tail p hp hd hc, Polynomial.eval_map] at he
    exact he
  let σ := RawTailComplexEmbedding.embedding C.tail hv α hroot
  refine ⟨σ, C.sound_of_root_realization input z hz h hv σ ?_⟩
  simpa only [σ, RawTailComplexEmbedding.embedding_generator] using hα.1

end InitialInputCandidate
end ComplexCSP.AlgebraicEncoding
