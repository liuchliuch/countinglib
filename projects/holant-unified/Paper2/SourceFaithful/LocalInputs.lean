import Paper2.SourceFaithful.Paper1Accepted
import Paper2.FixedFieldOutput.Reductions
import Paper2.ExactInput.FactorClosure
import Paper2.ExactInput.Normalization

/-! Separately named exact source inputs used by local construction routes.
These contain no Paper 2 terminal alternative, Bell reduction or codec theorem.
Signature inputs still use their original strict exact tables. -/
namespace Paper2.SourceFaithful
open Tractable ExactInput

structure Paper1RestrictionAccepted where
  restriction_2_5 : ∀ source target : Language, source.family ⊆ target.family →
    FixedFieldOutput.Reduces .nativeX source target

structure Paper1DirectGadgetAccepted where
  directGadget_2_5 : ∀ source augmented : Language,
    source.family ⊆ augmented.family →
    (∀ f ∈ augmented.family, NativeNetworkRealizesUpTo source.family f.2) →
      FixedFieldOutput.Reduces .nativeX augmented source

structure Paper1UnaryAccepted where
  unary_3_4 : ∀ L : Language, ∀ u : Signature AlgebraicComplex 1,
    u ≠ 0 → (⟨1,u⟩ : AnySignature AlgebraicComplex) ∈ L.family →
      Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L

structure Paper1EOAccepted where
  eo_2_16 : ∀ L : Language, Preprocessed L.family → (∀ g ∈ L.family, IsEO g) →
    (EOTract L.family → FixedFieldOutput.BooleanFP .nativeX L) ∧
    (¬ EOTract L.family → FixedFieldOutput.SharpPHard .nativeX L)

structure Paper1FactorClosureAccepted where
  factorClosure_2_23 : ∀ L : Language, Preprocessed L.family →
    ¬ CommonOneSided L.family → ∀ D : PrimeFactorization L, ∀ M : Language,
      M.family = L.family ∪ D.factors →
        FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M

structure Paper1NormalizationAccepted where
  normalization_2_26 : ∀ L : Language, Preprocessed L.family →
    ∀ D : InvertibleKernel, XConformal D → ∀ M : Language,
      M.family = familyAction D L.family →
        FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M

namespace Paper1DirectGadgetAccepted
 theorem adjoin (P : Paper1DirectGadgetAccepted) (L : Language) {n : ℕ}
    (f : Signature AlgebraicComplex n) (hf : NativeNetworkRealizesUpTo L.family f) :
    ∃ M : Language, M.family = insert (⟨n,f⟩ : AnySignature AlgebraicComplex) L.family ∧
      FixedFieldOutput.Reduces .nativeX M L := by
  obtain ⟨M,hM⟩ := Language.coverage_family _ (L.family_finite.insert ⟨n,f⟩)
  refine ⟨M,hM,P.directGadget_2_5 L M ?_ ?_⟩
  · rw [hM]; exact Set.subset_insert _ _
  · intro g hg
    rw [hM] at hg
    rcases hg with rfl | hg
    · exact hf
    · exact NativeNetworkRealizesUpTo.of_mem hg
 theorem adjoin_realizable (P : Paper1DirectGadgetAccepted) (L : Language) {n : ℕ}
    (f : Signature AlgebraicComplex n) (hf : NetworkRealizable L.family f) :
    ∃ M : Language, M.family = insert (⟨n,f⟩ : AnySignature AlgebraicComplex) L.family ∧
      FixedFieldOutput.Reduces .nativeX M L :=
  P.adjoin L f (NativeNetworkRealizesUpTo.of_realizable hf)
end Paper1DirectGadgetAccepted

namespace Paper1FactorClosureAccepted
 theorem factorClosure_2_19 (P : Paper1FactorClosureAccepted) (L : Language)
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (D : PrimeFactorization L) :
    ∃ M : Language, M.family = L.family ∪ D.factors ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  obtain ⟨M,hM⟩ := Language.coverage_family _ (L.family_finite.union D.factors_finite)
  exact ⟨M,hM,P.factorClosure_2_23 L hpre htwo D M hM⟩
end Paper1FactorClosureAccepted

namespace Paper1NormalizationAccepted
 theorem normalize (P : Paper1NormalizationAccepted) (L : Language)
    (hL : Preprocessed L.family) (D : InvertibleKernel) (hD : XConformal D) :
    ∃ M : Language, M.family = familyAction D L.family ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  obtain ⟨M,hM⟩ := Language.coverage_family _ (L.family_finite.image _)
  exact ⟨M,hM,P.normalization_2_26 L hL D hD M hM⟩
end Paper1NormalizationAccepted

end Paper2.SourceFaithful
