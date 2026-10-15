import Paper2.SourceFaithful.LocalInputs
import Paper2.HeightTwo.OriginalLanguage

/-! Complete source height-two classification with the explicitly chosen
canonical fixed-field answer protocol. The pure prime/decomposable algebra and
literal normalization are shared with the prior conditional root-output layer;
all machine reductions are reconstructed using the source-faithful inputs. -/
namespace Paper2.SourceFaithful.HeightTwo
open Tractable ExactInput
open Paper2.HeightTwo

/-- The conclusion concerns the entire retained language and its actual native
problem, not merely the isolated binary signature. -/
theorem weightedEquality_language_classification
    (P : Paper1Accepted) (PN : Paper1NormalizationAccepted)
    (L : Language) (hL : Preprocessed L.family)
    (f : Signature AlgebraicComplex 2) (hf : WeightedEquality f)
    (hmem : (⟨2, f⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
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
    exact ((P.literalEqualityDichotomy_2_23 M heq).2 hn).transport hML


/-- Complete prime/decomposable branch split for a retained preprocessed family.
The hard alternative is the original actual polynomial-time Turing problem. -/
theorem eightVertex_classification_preprocessed
    (P : Paper1Accepted) (PF : Paper1FactorClosureAccepted)
    (PN : Paper1NormalizationAccepted) (L : Language) (hL : Preprocessed L.family)
    (f : Signature AlgebraicComplex 4)
    (hmem : (⟨4, f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (heven : EvenSupport f) (h0 : f (fun _ => false) ≠ 0)
    (h1 : f (fun _ => true) ≠ 0) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases htract : Tract (kImage L)
  · exact Or.inl htract
  · right
    rcases prime_or_weightedEquality_product f heven h0 h1 with hp | ⟨A, B, e, he, hA, hB⟩
    · apply (P.primeQuaternary_1_3 L ?_).2 htract
      refine ⟨f, hmem, hp, ?_, mul_ne_zero h0 h1⟩
      intro x ho
      by_contra hz
      obtain ⟨a, ha⟩ := heven x hz
      obtain ⟨b, hb⟩ := ho
      omega
    · let DA := TensorDecomposition.singleton A
      let DB := TensorDecomposition.singleton B
      let Q := (DA.append DB).reindex e
      have hQ : Q.value = f := by
        rw [TensorDecomposition.value_reindex, TensorDecomposition.value_append]
        simpa only [DA, DB, TensorDecomposition.value_singleton] using he
      have hpos : ∀ j, 0 < Q.arity j :=
        TensorDecomposition.factors_append DA DB (fun r _ => 0 < r)
          (fun _ => by change 0 < 2; decide) (fun _ => by change 0 < 2; decide)
      have hprime : ∀ j, TensorPrime (Q.factor j) :=
        TensorDecomposition.factors_append DA DB (fun _ g => TensorPrime g)
          (fun _ => weightedEquality_tensorPrime A hA)
          (fun _ => weightedEquality_tensorPrime B hB)
      obtain ⟨D, hD⟩ := PrimeFactorization.exists_with_member_decomposition L hL f hmem Q hQ hpos hprime
      let iA : Fin DA.count := ⟨0, by change 0 < 1; decide⟩
      let jA : Fin Q.count := DA.appendIndexLeft DB iA
      have hAmem : (⟨2, A⟩ : AnySignature AlgebraicComplex) ∈ D.factors := by
        have hh := hD jA
        change (⟨(DA.append DB).arity (DA.appendIndexLeft DB iA),
          (DA.append DB).factor (DA.appendIndexLeft DB iA)⟩ : AnySignature AlgebraicComplex) ∈ D.factors at hh
        rw [TensorDecomposition.append_factor_left] at hh
        exact hh
      have htwo := two_endpoints_not_commonOneSided (by decide : 0 < 4) L.family f hmem h0 h1
      obtain ⟨M, hM, hML, hLM⟩ := PF.factorClosure_2_19 L hL htwo D
      have hpreM : Preprocessed M.family := by
        rw [hM]
        exact preprocessed_factor_union D hL
      have hAmemM : (⟨2, A⟩ : AnySignature AlgebraicComplex) ∈ M.family := by
        rw [hM]
        exact Or.inr hAmem
      rcases weightedEquality_language_classification P PN M hpreM A hA hAmemM with ht | hh
      · exfalso
        apply htract
        exact ht.mono_family (familyAction_mono sourceKBasis (by
          rw [hM]; exact Set.subset_union_left))
      · exact hh.transport hML

/-- Section 6's height-two conclusion, with the paper's preprocessing convention
explicit. No charge divisibility of the ambient family is required. -/
theorem mountain_classification_preprocessed
    (P : Paper1Accepted) (PF : Paper1FactorClosureAccepted)
    (PN : Paper1NormalizationAccepted) (L : Language) (hL : Preprocessed L.family)
    (f : Signature AlgebraicComplex 4)
    (hmem : (⟨4, f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hm : IsMountain (d := 2) f) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L :=
  eightVertex_classification_preprocessed P PF PN L hL f hmem
    (mountain_evenSupport f hm) hm.zero_ne_zero hm.one_ne_zero


/-- Actual zero and nullary input labels remain permitted in the original L.
Only the structural classification runs on its preprocessed finite subfamily.
The public-output bound parameter is a separately recorded outstanding bridge. -/
theorem mountain_classification
    (P : Paper1Accepted) (PF : Paper1FactorClosureAccepted)
    (PN : Paper1NormalizationAccepted) (PR : Paper1RestrictionAccepted)
    (L : Language)
    (f : Signature AlgebraicComplex 4)
    (hmem : (⟨4, f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hm : IsMountain (d := 2) f) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
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
  · exact Or.inr (hh.transport (PR.restriction_2_5 M L (by rw [hM]; exact fun _ h => h.1)))


end Paper2.SourceFaithful.HeightTwo

