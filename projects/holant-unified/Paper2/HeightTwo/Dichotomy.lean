import Paper2.HeightTwo.EqualityBranch
import Paper2.HeightTwo.Primality
import Paper2.PrimeFactorization
import Paper2.Tractable.Downward

/-! The height-two route for preprocessed literal languages. Tensor factor
existence, exact weighted equality normalization, and all seven-clause transport
are proved. The only source inputs are the separately named permitted Paper 1
classification/factor/coordinate reduction records. -/
namespace Paper2.HeightTwo
open Tractable ExactInput

lemma two_endpoints_not_commonOneSided {n : ℕ} (hn : 0 < n)
    (F : SignatureFamily AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (hf : (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h0 : f (fun _ => false) ≠ 0) (h1 : f (fun _ => true) ≠ 0) :
    ¬ CommonOneSided F := by
  rintro (h | h)
  · have hh := h ⟨n, f⟩ hf _ h0
    simp only [charge, weight_false, Nat.cast_zero, mul_zero, zero_sub] at hh
    have : (0 : ℤ) < n := by exact_mod_cast hn
    omega
  · have hh := h ⟨n, f⟩ hf _ h1
    simp only [charge, weight_true, Fintype.card_fin] at hh
    have : (0 : ℤ) < n := by exact_mod_cast hn
    omega

lemma preprocessed_factor_union {L : Language} (D : PrimeFactorization L)
    (hL : Preprocessed L.family) : Preprocessed (L.family ∪ D.factors) := by
  intro g hg
  rcases hg with hg | ⟨⟨i, j⟩, rfl⟩
  · exact hL g hg
  · exact ⟨D.positive i j, (D.prime i j).1⟩

/-- Complete prime/decomposable branch split for a retained preprocessed family.
The hard alternative is the original actual polynomial-time Turing problem. -/
theorem eightVertex_classification_preprocessed
    (P : Paper1Accepted) (PF : Paper1FactorClosureAccepted)
    (PN : Paper1NormalizationAccepted) (L : Language) (hL : Preprocessed L.family)
    (f : Signature AlgebraicComplex 4)
    (hmem : (⟨4, f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (heven : EvenSupport f) (h0 : f (fun _ => false) ≠ 0)
    (h1 : f (fun _ => true) ≠ 0) :
    Tract (kImage L) ∨ Problem.SharpPHard .nativeX L := by
  classical
  by_cases htract : Tract (kImage L)
  · exact Or.inl htract
  · right
    rcases prime_or_weightedEquality_product f heven h0 h1 with hp | ⟨A, B, e, he, hA, hB⟩
    · apply (P.primeQuaternaryDichotomy_2_24 L ?_).2 htract
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
      · exact hh.transport_equivalence hML hLM

/-- Section 6's height-two conclusion, with the paper's preprocessing convention
explicit. No charge divisibility of the ambient family is required. -/
theorem mountain_classification_preprocessed
    (P : Paper1Accepted) (PF : Paper1FactorClosureAccepted)
    (PN : Paper1NormalizationAccepted) (L : Language) (hL : Preprocessed L.family)
    (f : Signature AlgebraicComplex 4)
    (hmem : (⟨4, f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hm : IsMountain (d := 2) f) :
    Tract (kImage L) ∨ Problem.SharpPHard .nativeX L :=
  eightVertex_classification_preprocessed P PF PN L hL f hmem
    (mountain_evenSupport f hm) hm.zero_ne_zero hm.one_ne_zero

end Paper2.HeightTwo
