import Paper2.HeightOne.UnsafeBinary
import Paper2.SourceFaithful.GadgetAugmentation
import Paper2.SourceFaithful.RelativeEO.BinaryEOAlternative

/-! The source height-one unsafe-binary terminal with canonical fixed-field
answers. Its literal graph, singular factorization, preprocessing, two-sided
charges and original-language reduction are identical mathematical data. -/
namespace Paper2.SourceFaithful.HeightOne
noncomputable section
open Tractable ExactInput
open Paper2.HeightOne Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup

/-- A singular or infinite-projective-order actual binary classifies the whole
original language, using only the exact cited Paper 1 interpolation input. -/
theorem unsafe_actual_binary_classification
    (PG : Paper1DirectGadgetAccepted) (PR : Paper1RestrictionAccepted)
    (PF : Paper1FactorClosureAccepted) (PU : Paper1UnaryAccepted)
    (PI : Paper1BinaryInterpolationAccepted) (L : Language)
    (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hunsafe : ¬ AllBinariesSafe L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases ht : Tract (kImage L)
  · exact Or.inl ht
  right
  have hbad : ∃ B : AMat, NetworkRealizable L.family (binarySignature B) ∧ B ≠ 0 ∧
      (Matrix.det B = 0 ∨ ¬ ProjectivelyFinite (transfer B)) := by
    unfold AllBinariesSafe at hunsafe
    push Not at hunsafe
    obtain ⟨B, hr, hn, hs⟩ := hunsafe
    refine ⟨B, hr, hn, ?_⟩
    by_cases hd : Matrix.det B = 0
    · exact Or.inl hd
    · exact Or.inr (hs hd)
  obtain ⟨B, hreal, hB, hbad⟩ := hbad
  obtain ⟨A, hA, hAL, _⟩ := PG.adjoin_equivalence PR L (binarySignature B)
    (NativeNetworkRealizesUpTo.of_realizable hreal)
  have hsub : L.family ⊆ A.family := by rw [hA]; exact Set.subset_insert _ _
  have hmem : (⟨2, binarySignature B⟩ : AnySignature AlgebraicComplex) ∈ A.family := by
    rw [hA]
    exact Set.mem_insert _ _
  have hpreA : Preprocessed A.family := by
    rw [hA]
    intro f hf
    rcases hf with rfl | hf
    · exact ⟨by change 0 < (2 : ℕ); decide, binarySignature_ne_zero hB⟩
    · exact hpre f hf
  have hbothA := bothChargeSigns_mono hsub hboth
  have hnotA : ¬ Tract (kImage A) :=
    fun h => ht (h.mono_family (familyAction_mono sourceKBasis hsub))
  have hhard : FixedFieldOutput.SharpPHard .nativeX A := by
    by_cases hd : Matrix.det B = 0
    · obtain ⟨u, v, hu, hv, hfac⟩ := singular_binary_factorization B hB hd
      apply SourceFaithful.RelativeEO.rankOne_binary_hard PF PU A hpreA
        (bothChargeSigns_not_commonOneSided hbothA) hnotA u v hu hv
      rwa [hfac]
    · have hinf : ¬ ProjectivelyFinite (transfer B) := hbad.resolve_left hd
      apply SourceFaithful.RelativeEO.infinite_transfer_hard PI PF PU A hpreA hbothA
        hnotA B hmem _ hinf
      rw [transfer, Matrix.det_mul]
      exact mul_ne_zero hd det_X_ne_zero
  exact hhard.transport hAL

end
end Paper2.SourceFaithful.HeightOne

