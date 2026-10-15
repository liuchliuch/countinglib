import Paper2.SourceFaithful.Synthesis.Complete
import Paper2.Paper1ProvedOddUnaryComplete
import Paper2.Paper1ProvedOddResidueUnaryReduction

/-! The manuscript's mountain classification with every source input proved.
The actual mountain supplies positive height and a nonzero table. Structural
preprocessing therefore retains it, while the final controlled reduction still
targets the original language, including its zero and nullary rows. -/
namespace Paper2.SourceFaithful.Synthesis
open Paper2.Tractable Paper2.ExactInput
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The four proved height cases instantiate the independent unary theorem,
its derived ordinary odd theorem, and every actual graph/source provider. -/
theorem mountain_classification_preprocessed
    (L : Language) (hpre : Preprocessed L.family) {d : ℕ}
    (heven : ∀ f ∈ L.family, Even f.1)
    (hdiv : 3 ≤ d → ∀ f ∈ L.family, Tensor.HalfChargeDivisible f.2 d)
    (M : Signature AlgebraicComplex (2*d)) (hM : IsMountain M)
    (hmem : (⟨2*d,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  let U := Paper2.Paper1Proved.OddUnary.UnaryProvider.proved
  let O := Paper2.Paper1Proved.OddResidue.oddProviderOfUnary
    Paper2.Paper1Proved.directGadgetProvider Paper2.Paper1Proved.restrictionProvider
    Paper2.Paper1Proved.factorProvider U
  have hd : 0 < d := hM.height_pos
  by_cases h1 : d=1
  · subst d
    exact HeightOne.mountain_classification_preprocessed
      Paper2.Paper1Proved.provider Paper2.Paper1Proved.directGadgetProvider
      Paper2.Paper1Proved.restrictionProvider Paper2.Paper1Proved.factorProvider
      Paper2.Paper1Proved.binaryInterpolationProvider O Paper2.Paper1Proved.normalizationProvider
      L hpre M hM hmem
  by_cases h2 : d=2
  · subst d
    exact HeightTwo.mountain_classification_preprocessed
      Paper2.Paper1Proved.provider Paper2.Paper1Proved.factorProvider
      Paper2.Paper1Proved.normalizationProvider L hpre M hmem hM
  by_cases h3 : d=3
  · subst d
    exact HeightThree.theorem_7_1
      Paper2.Paper1Proved.directGadgetProvider Paper2.Paper1Proved.occurrenceProvider
      Paper2.Paper1Proved.factorProvider U Paper2.Paper1Proved.eoProvider
      Paper2.Paper1Proved.restrictionProvider L heven (hdiv (by omega)) M hM hmem
  exact HighHeight.classification_ge_four
    Paper2.Paper1Proved.provider Paper2.Paper1Proved.directGadgetProvider
    Paper2.Paper1Proved.occurrenceProvider Paper2.Paper1Proved.factorProvider U
    Paper2.Paper1Proved.eoProvider Paper2.Paper1Proved.restrictionProvider
    Paper2.Paper1Proved.binaryInterpolationProvider Paper2.Paper1Proved.normalizationProvider
    L (by omega) hpre heven (hdiv (by omega)) M hM hmem

/-- Whole-language mountain classification. The supported half-charge
divisibility promise is needed only at heights at least three. No accepted
provider, classifier, retained-stage terminal, or compiler is an input. -/
theorem mountain_classification
    (L : Language) {d : ℕ}
    (heven : ∀ f ∈ L.family, Even f.1)
    (hdiv : 3 ≤ d → ∀ f ∈ L.family, Tensor.HalfChargeDivisible f.2 d)
    (M : Signature AlgebraicComplex (2*d)) (hM : IsMountain M)
    (hmem : (⟨2*d,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨N,hN⟩ := Language.coverage_family (preprocess L.family)
    (L.family_finite.subset (fun _ h=>h.1))
  apply classification_from_preprocessed Paper2.Paper1Proved.restrictionProvider L N hN
  apply mountain_classification_preprocessed N
  · rw [hN]
    exact preprocess_preprocessed _
  · intro f hf
    rw [hN] at hf
    exact heven f hf.1
  · intro hd f hf
    rw [hN] at hf
    exact hdiv hd f hf.1
  · exact hM
  · rw [hN]
    refine ⟨hmem,?_,?_⟩
    · have hd := hM.height_pos
      change 0 < 2*d
      omega
    · intro hz
      exact hM.zero_ne_zero (congrFun hz _)

/-- Source Theorem 9.1 on the original finite native-X problem. -/
theorem theorem_9_1
    (L : Language) {d : ℕ}
    (heven : ∀ f ∈ L.family, Even f.1)
    (hdiv : 3 ≤ d → ∀ f ∈ L.family, Tensor.HalfChargeDivisible f.2 d)
    (M : Signature AlgebraicComplex (2*d)) (hM : IsMountain M)
    (hmem : (⟨2*d,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L :=
  mountain_classification L heven hdiv M hM hmem

end
end Paper2.SourceFaithful.Synthesis

