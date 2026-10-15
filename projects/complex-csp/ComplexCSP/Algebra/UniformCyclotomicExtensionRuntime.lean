import ComplexCSP.Algebra.UniformCyclotomicExtensionValidation
import ComplexCSP.Algebra.UniformCyclotomicExtensionConjugation
import ComplexCSP.Algebra.EncodedNumberFieldPowerBasis

/-!
# Runtime fields and embeddings for accepted extension candidates

Candidate acceptance constructs the field dictionary from checked input. The
embedding itself executes finite rational substitution; abstract power-basis
lifts occur only in its correctness proofs.
-/
set_option backward.isDefEq.respectTransparency false

namespace ComplexCSP.AlgebraicEncoding
open Polynomial EncodedNumberField

variable {n : ℕ}

 theorem candidate_valid {r : ℕ} (old : Fin r → ℤ) (δ : ℕ)
    (C : CyclotomicCandidate) (hC : C.test old δ = true) :
    Element.Valid C.dimension C.relation :=
  Element.valid_of_irreducibleMonicTail C.tail (of_decide_eq_true hC).2.2.1

/-- The executable carrier itself is an actual model, with the same stored coordinates. -/
noncomputable def coordinateFieldModel (n : ℕ) (c : CoeffVector n) [Fact (Element.Valid n c)] :
    Element.Model n c where
  K := Element n c
  field := inferInstance
  algebra := inferInstance
  generator := Element.generator
  basis := Element.powerBasis.basis
  basis_eq_pow := Element.powerBasis.basis_eq_pow
  relation := Element.generator_relation

 theorem coordinateField_minpoly (a : Fin n → ℤ)
    (ha : MonicIrreducibility.irreducibleMonicTail a = true)
    [Fact (Element.Valid n (EffectiveRoots.coefficientRelation a))] :
    (MonicIrreducibility.denote (MonicIrreducibility.fromTail a)).map (Int.castRingHom ℚ) =
      minpoly ℚ (Element.generator (c := EffectiveRoots.coefficientRelation a)) := by
  let M := coordinateFieldModel n (EffectiveRoots.coefficientRelation a)
  letI := modelNumberField M
  exact (validatedIntegralPresentation a ha M).map_eq_minpoly

section Accepted
variable (old : Fin n → ℤ) (ha : MonicIrreducibility.irreducibleMonicTail old = true)
  (δ : ℕ) (hδ : 0 < δ) (C : CyclotomicCandidate) (hC : C.test old δ = true)

variable [Fact (Element.Valid n (EffectiveRoots.coefficientRelation old))]
  [Fact (Element.Valid C.dimension C.relation)]

include hδ hC in
omit [Fact (Element.Valid n (EffectiveRoots.coefficientRelation old))] in
 theorem acceptedCandidate_equations :
    aeval (⟨C.oldGenerator⟩ : Element C.dimension C.relation)
      (MonicIrreducibility.denote (MonicIrreducibility.fromTail old)) = 0 ∧
    IsPrimitiveRoot (⟨C.root⟩ : Element C.dimension C.relation) δ ∧
    Element.generator (c := C.relation) =
      (C.d : Element C.dimension C.relation) * ⟨C.oldGenerator⟩ +
        (C.m : Element C.dimension C.relation) * ⟨C.root⟩ := by
  have h := (candidateTest_correct_in_model
    (Element.powerBasis (c := C.relation)) C.tail C.oldGenerator C.root C.d C.m
    old δ hδ Element.generator_relation).mp hC
  simpa only [Element.powerBasis_gen, Element.interpret_generator] using h.2.2

include ha hδ hC in
 theorem acceptedCandidate_old_root :
    aeval (⟨C.oldGenerator⟩ : Element C.dimension C.relation)
      (minpoly ℚ (Element.generator (c := EffectiveRoots.coefficientRelation old))) = 0 := by
  rw [← coordinateField_minpoly old ha]
  change aeval (⟨C.oldGenerator⟩ : Element C.dimension C.relation)
    ((MonicIrreducibility.denote (MonicIrreducibility.fromTail old)).map (algebraMap ℤ ℚ)) = 0
  rw [aeval_map_algebraMap]
  exact (acceptedCandidate_equations old δ hδ C hC).1

/-- Runtime map on old-field coordinates. -/
def candidateEmbeddingValue
    (x : Element n (EffectiveRoots.coefficientRelation old)) : Element C.dimension C.relation :=
  ⟨evaluateCoordinates C.relation C.oldGenerator x.coeff⟩

include ha hδ hC in
 theorem candidateEmbeddingValue_eq_lift
    (x : Element n (EffectiveRoots.coefficientRelation old)) :
    candidateEmbeddingValue old C x =
      (Element.powerBasis (c := EffectiveRoots.coefficientRelation old)).lift
        (⟨C.oldGenerator⟩ : Element C.dimension C.relation)
        (acceptedCandidate_old_root old ha δ hδ C hC) x := by
  let ψ := (Element.powerBasis (c := EffectiveRoots.coefficientRelation old)).lift
    (⟨C.oldGenerator⟩ : Element C.dimension C.relation)
    (acceptedCandidate_old_root old ha δ hδ C hC)
  have hψ : ψ Element.generator = ⟨C.oldGenerator⟩ := PowerBasis.lift_gen _ _ _
  change (⟨evaluateCoordinates C.relation C.oldGenerator x.coeff⟩ :
    Element C.dimension C.relation) = ψ x
  rw [← Element.interpret_generator, interpret_evaluateCoordinates _ _ _ _
    (show 0 < C.dimension from (Element.powerBasis (c := C.relation)).dim_pos) Element.generator_relation,
    Element.interpret_generator]
  have hx : interpret (Element.generator (c := EffectiveRoots.coefficientRelation old))
      x.coeff = x := Element.interpret_generator x.coeff
  conv_rhs => rw [← hx]
  have hm := map_interpret ψ.toRingHom
    (Element.generator (c := EffectiveRoots.coefficientRelation old)) x.coeff
  change ψ (interpret Element.generator x.coeff) = interpret (ψ Element.generator) x.coeff at hm
  rw [hψ] at hm
  exact hm.symm

/-- A genuine, executable field embedding obtained from the finite test. -/
def candidateEmbedding :
    Element n (EffectiveRoots.coefficientRelation old) →+* Element C.dimension C.relation where
  toFun := candidateEmbeddingValue old C
  map_one' := by rw [candidateEmbeddingValue_eq_lift old ha δ hδ C hC]; exact map_one _
  map_mul' x y := by
    simp only [candidateEmbeddingValue_eq_lift old ha δ hδ C hC, map_mul]
  map_zero' := by rw [candidateEmbeddingValue_eq_lift old ha δ hδ C hC]; exact map_zero _
  map_add' x y := by
    simp only [candidateEmbeddingValue_eq_lift old ha δ hδ C hC, map_add]

include ha hδ hC in
 theorem candidateEmbedding_generator :
    candidateEmbedding old ha δ hδ C hC Element.generator = ⟨C.oldGenerator⟩ := by
  change candidateEmbeddingValue old C Element.generator = _
  rw [candidateEmbeddingValue_eq_lift old ha δ hδ C hC]
  exact PowerBasis.lift_gen _ _ _

include hδ hC in
omit [Fact (Element.Valid n (EffectiveRoots.coefficientRelation old))] in
/-- An accepted candidate is generated by the old generator and new root. -/
theorem acceptedCandidate_generated :
    IntermediateField.adjoin ℚ
      ({(⟨C.oldGenerator⟩ : Element C.dimension C.relation), ⟨C.root⟩} :
        Set (Element C.dimension C.relation)) = ⊤ := by
  apply adjoin_pair_top_of_generator (Element.powerBasis (c := C.relation))
    (⟨C.oldGenerator⟩ : Element C.dimension C.relation) ⟨C.root⟩ C.d C.m
  exact (acceptedCandidate_equations old δ hδ C hC).2.2

include ha hδ hC in
/-- The old verified conjugation yields verified executable conjugation on the
new field, along an extension of the same chosen complex embedding. -/
theorem candidate_conjugation_valid (oldConjugate : CoeffVector n)
    (hstar : Element.StarValid n (EffectiveRoots.coefficientRelation old) oldConjugate) :
    Element.StarValid C.dimension C.relation
      (extensionConjugateCoordinates C.relation C.oldGenerator C.root oldConjugate C.d C.m) := by
  obtain ⟨M, e, he⟩ := hstar
  let φ := e.comp M.valueRingEquiv.toRingHom
  have hφgen : φ (Element.generator (c := EffectiveRoots.coefficientRelation old)) =
      e M.generator := congrArg e M.value_generator
  have hφ : interpret (φ (Element.generator (c := EffectiveRoots.coefficientRelation old)))
      oldConjugate = star (φ Element.generator) := by rw [hφgen]; exact he
  obtain ⟨Φ, hΦ⟩ := exists_complex_embedding_extension
    (candidateEmbedding old ha δ hδ C hC) φ
  have hΦa : Φ (⟨C.oldGenerator⟩ : Element C.dimension C.relation) =
      φ (Element.generator (c := EffectiveRoots.coefficientRelation old)) := by
    rw [← candidateEmbedding_generator old ha δ hδ C hC]
    exact RingHom.congr_fun hΦ Element.generator
  have heq := acceptedCandidate_equations old δ hδ C hC
  refine ⟨coordinateFieldModel C.dimension C.relation, Φ, ?_⟩
  exact extensionConjugateCoordinates_correct
    (Element.powerBasis (c := C.relation)) C.relation C.oldGenerator C.root
    Element.generator_relation oldConjugate C.d C.m
    (by simpa only [Element.powerBasis_gen, Element.interpret_generator] using heq.2.2)
    δ hδ (by simpa only [Element.powerBasis_gen, Element.interpret_generator] using heq.2.1) Φ
    (by simpa only [Element.powerBasis_gen, Element.interpret_generator, hΦa] using hφ)

end Accepted
/-- Closed executable embedding API: both field validations come from the finite
input/candidate checks, rather than caller-supplied semantic field structures. -/
def validatedCandidateEmbedding (old : Fin n → ℤ)
    (ha : MonicIrreducibility.irreducibleMonicTail old = true)
    (δ : ℕ) (hδ : 0 < δ) (C : CyclotomicCandidate) (hC : C.test old δ = true) :
    letI : Fact (Element.Valid n (EffectiveRoots.coefficientRelation old)) :=
      ⟨Element.valid_of_irreducibleMonicTail old ha⟩
    letI : Fact (Element.Valid C.dimension C.relation) := ⟨candidate_valid old δ C hC⟩
    Element n (EffectiveRoots.coefficientRelation old) →+* Element C.dimension C.relation := by
  letI : Fact (Element.Valid n (EffectiveRoots.coefficientRelation old)) :=
    ⟨Element.valid_of_irreducibleMonicTail old ha⟩
  letI : Fact (Element.Valid C.dimension C.relation) := ⟨candidate_valid old δ C hC⟩
  exact candidateEmbedding old ha δ hδ C hC

/-- Closed conjugation API for an accepted raw candidate. The old conjugate
vector is the explicitly validated input conjugation, not an extension oracle. -/
theorem validatedCandidate_conjugation (old : Fin n → ℤ)
    (ha : MonicIrreducibility.irreducibleMonicTail old = true)
    (δ : ℕ) (hδ : 0 < δ) (C : CyclotomicCandidate) (hC : C.test old δ = true)
    (oldConjugate : CoeffVector n)
    (hstar : Element.StarValid n (EffectiveRoots.coefficientRelation old) oldConjugate) :
    Element.StarValid C.dimension C.relation
      (extensionConjugateCoordinates C.relation C.oldGenerator C.root oldConjugate C.d C.m) := by
  letI : Fact (Element.Valid n (EffectiveRoots.coefficientRelation old)) :=
    ⟨Element.valid_of_irreducibleMonicTail old ha⟩
  letI : Fact (Element.Valid C.dimension C.relation) := ⟨candidate_valid old δ C hC⟩
  exact candidate_conjugation_valid old ha δ hδ C hC oldConjugate hstar

end ComplexCSP.AlgebraicEncoding
