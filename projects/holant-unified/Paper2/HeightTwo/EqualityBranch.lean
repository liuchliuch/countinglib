import Paper2.HeightTwo.Normalization
import Paper2.ExactInput.Normalization

/-! The exact weighted-equality branch, composing proved table normalization
with only the accepted source equality theorem and legal coordinate reduction. -/
namespace Paper2.HeightTwo
open Tractable ExactInput

/-- The conclusion concerns the entire retained language and its actual native
problem, not merely the isolated binary signature. -/
theorem weightedEquality_language_classification
    (P : Paper1Accepted) (PN : Paper1NormalizationAccepted)
    (L : Language) (hL : Preprocessed L.family)
    (f : Signature AlgebraicComplex 2) (hf : WeightedEquality f)
    (hmem : (⟨2, f⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (kImage L) ∨ Problem.SharpPHard .nativeX L := by
  classical
  by_cases ht : Tract (kImage L)
  · exact Or.inl ht
  · right
    obtain ⟨D, hD, hDf⟩ := weightedEquality_normalization f hf
    obtain ⟨M, hM, hML, hLM⟩ := PN.normalize L hL D hD
    have heq : HasLiteralEquality M := by
      change (⟨2, kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex) ∈ M.family
      rw [hM]
      exact ⟨⟨2, f⟩, hmem, by simp only [hDf]⟩
    have hn : ¬ Tract (kImage M) := by
      intro hh
      apply ht
      apply (xConformal_tract_iff hD L.family).mpr
      simpa only [kImage, hM] using hh
    exact ((P.literalEqualityDichotomy_2_23 M heq).2 hn).transport_equivalence hML hLM

end Paper2.HeightTwo
