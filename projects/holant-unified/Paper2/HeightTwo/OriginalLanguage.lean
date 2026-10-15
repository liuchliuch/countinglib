import Paper2.HeightTwo.Dichotomy
import Paper2.Paper1Accepted.Terminals
import Paper2.Tractable.CriteriaFacts

/-! The zero/nullary family boundary, with the still-independent public-output
size obligation explicit. This is an integration adapter, not a claim that the
unconditional original-language theorem has already been completed. -/
namespace Paper2.HeightTwo
open Tractable ExactInput

/-- Structural preprocessing commutes with the one shared K matrix. -/
lemma kImage_preprocessed_tract_iff (L M : Language)
    (hM : M.family = preprocess L.family) : Tract (kImage M) ↔ Tract (kImage L) := by
  simp only [kImage, hM, ← Conformal.preprocess_familyAction]
  exact tract_preprocess _

/-- Actual zero and nullary input labels remain permitted in the original L.
Only the structural classification runs on its preprocessed finite subfamily.
The public-output bound parameter is a separately recorded outstanding bridge. -/
theorem mountain_classification_original_of_bounded_answers
    (P : Paper1Accepted) (PF : Paper1FactorClosureAccepted)
    (PN : Paper1NormalizationAccepted) (PR : Paper1RestrictionAccepted)
    (L : Language) (hanswers : Nonempty (Problem.BoundedAnswers .nativeX L))
    (f : Signature AlgebraicComplex 4)
    (hmem : (⟨4, f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hm : IsMountain (d := 2) f) :
    Tract (kImage L) ∨ Problem.SharpPHard .nativeX L := by
  obtain ⟨M, hM⟩ := Language.coverage_family (preprocess L.family)
    (L.family_finite.subset (fun _ h => h.1))
  have hpre : Preprocessed M.family := by
    rw [hM]
    exact preprocess_preprocessed _
  have hmemM : (⟨4, f⟩ : AnySignature AlgebraicComplex) ∈ M.family := by
    rw [hM]
    refine ⟨hmem, by change 0 < 4; decide, ?_⟩
    intro hz
    exact hm.zero_ne_zero (congrFun hz _)
  rcases mountain_classification_preprocessed P PF PN M hpre f hmemM hm with ht | hh
  · exact Or.inl ((kImage_preprocessed_tract_iff L M hM).mp ht)
  · exact Or.inr (hh.transport (PR.restriction_2_5 M L (by rw [hM]; exact fun _ h => h.1)) hanswers)

end Paper2.HeightTwo
