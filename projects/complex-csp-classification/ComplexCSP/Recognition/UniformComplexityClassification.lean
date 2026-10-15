import ComplexCSP.Complexity.Classification
import ComplexCSP.Recognition.UniformAlgebraicEncoded

/-! # Uniform recognition and fixed-language complexity implications

The terminating recognizer takes integer-polynomial and isolating-rectangle
descriptions. A finite rational basis specifies exact partition outputs. Both
complexity implications use proved bit-machine programs and charged reductions.
Recognition uses the corrected all-instance Theorem 5.2. -/
namespace ComplexCSP.Recognition
open PlanarHom PlanarHom.Complexity AlgebraicEncoding
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {dimension : ℕ}

/-- The exact original encoded input decides which proved ordinary branch
applies, in every supplied finite rational-basis realization of its values. -/
theorem encodedGlobalTest_complexity (L : FiniteAlgebraicLanguage) (hL : L.Valid)
    (z : ∀ i, (Fin (L.tables.arity i) → Fin L.domainSize) → ℂ)
    (hz : ∀ i a, (L.tables.value i a).Represents (z i a))
    (M : Language (Fin L.domainSize) K (Fin L.signatureSize))
    (basis : Module.Basis (Fin dimension) ℚ K) (σ : K →+* ℂ)
    (hM : M.mapValues σ=realizedAlgebraicLanguage L.tables z) :
    (encodedGlobalTest L hL=true → (ComplexityCSPCountReduction.partitionProblem M basis).InFP) ∧
    (encodedGlobalTest L hL=false → PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem M basis)) := by
  letI : NeZero L.domainSize := ⟨Nat.ne_zero_of_lt L.domain_pos⟩
  have hc := encodedGlobalTest_correct L hL z hz
  rw [←hM] at hc
  constructor
  · intro ht
    exact ComplexityPositiveFP.conditions_inFP M basis σ (hc.mp ht)
  · intro hf
    apply ComplexityNonBOHardness.hard_of_not_conditions basis σ M
    intro h
    have ht := hc.mpr h
    rw [hf] at ht
    contradiction

/-- Corollary 1.2's final complexity-side interpretation, with the positive
modulus as runtime data and exact occurrence-multiplicity semantics. -/
theorem encodedDegreeGlobalTest_complexity (L : FiniteAlgebraicLanguage) (hL : L.Valid)
    (δ : ℕ) (hδ : 0<δ)
    (z : ∀ i, (Fin (L.tables.arity i) → Fin L.domainSize) → ℂ)
    (hz : ∀ i a, (L.tables.value i a).Represents (z i a))
    (M : Language (Fin L.domainSize) K (Fin L.signatureSize))
    (basis : Module.Basis (Fin dimension) ℚ K) (σ : K →+* ℂ)
    (hM : M.mapValues σ=realizedAlgebraicLanguage L.tables z) :
    (encodedDegreeGlobalTest L hL δ hδ=true → (ComplexityGadgetSubstitution.degreePartitionProblem M basis δ).InFP) ∧
    (encodedDegreeGlobalTest L hL δ hδ=false → PromisedSharpPHard (ComplexityGadgetSubstitution.degreePartitionProblem M basis δ)) := by
  letI : NeZero L.domainSize := ⟨Nat.ne_zero_of_lt L.domain_pos⟩
  have hc := encodedDegreeGlobalTest_correct L hL δ hδ z hz
  rw [←hM] at hc
  constructor
  · intro ht
    exact ComplexityPositiveFP.degreeConditions_inFP M basis σ hδ (hc.mp ht)
  · intro hf
    apply ComplexityDegreeHardness.hard_of_not_degreeConditions basis σ M δ hδ
    intro h
    have ht := hc.mpr h
    rw [hf] at ht
    contradiction

end ComplexCSP.Recognition
