import Paper2.HeightOne.PhaseCards.FactorSaturation
import Paper2.RelativeEO.Paper1BinaryAccepted

/-! Unsafe actual binaries terminate the height-one route using only the
named Paper 1 interpolation/factor/unary inputs. An actual binary is first
adjoined to a real finite language; no formal matrix is treated as available. -/
namespace Paper2.HeightOne
noncomputable section
open Tractable ExactInput GroupSplit GroupSplit.MatrixGroup RelativeEO

/-- Every nonzero singular ordered 2×2 table is an actual product of two
nonzero unary tables, with the division scalar displayed explicitly. -/
theorem singular_binary_factorization (B : AMat) (hB : B ≠ 0) (hdet : Matrix.det B = 0) :
    ∃ u v : Signature AlgebraicComplex 1, u ≠ 0 ∧ v ≠ 0 ∧
      Signature.tensor u v = binarySignature B := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, B i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hB (funext (fun i => funext (h i)))
  let u : Signature AlgebraicComplex 1 := fun x => B (x 0) j
  let v : Signature AlgebraicComplex 1 := fun x => B i (x 0) / B i j
  refine ⟨u, v, ?_, ?_, ?_⟩
  · intro hz
    exact hij (congrFun hz (fun _ => i))
  · intro hz
    have h := congrFun hz (fun _ => j)
    change B i j / B i j = 0 at h
    rw [div_self hij] at h
    exact one_ne_zero h
  · have hd := hdet
    rw [determinant_bool] at hd
    have hminor (a b : Bool) : B a j * B i b = B a b * B i j := by
      cases i <;> cases j <;> cases a <;> cases b <;> dsimp at * <;> first | ring | linear_combination hd | linear_combination -hd
    funext x
    change B (x 0) j * (B i (x 1) / B i j) = B (x 0) (x 1)
    rw [← mul_div_assoc, div_eq_iff hij]
    exact hminor _ _

lemma bothChargeSigns_not_commonOneSided {F : SignatureFamily AlgebraicComplex}
    (h : BothChargeSigns F) : ¬ CommonOneSided F := by
  obtain ⟨⟨f, hf, x, hx, hn⟩, ⟨g, hg, y, hy, hp⟩⟩ := h
  rintro (h | h)
  · exact (not_le_of_gt hn) (h f hf x hx)
  · exact (not_le_of_gt hp) (h g hg y hy)

lemma bothChargeSigns_mono {F G : SignatureFamily AlgebraicComplex}
    (hFG : F ⊆ G) (h : BothChargeSigns F) : BothChargeSigns G := by
  obtain ⟨⟨f, hf, x, hx, hn⟩, ⟨g, hg, y, hy, hp⟩⟩ := h
  exact ⟨⟨f, hFG hf, x, hx, hn⟩, ⟨g, hFG hg, y, hy, hp⟩⟩

/-- The bad binary is genuinely network-realizable over the original language.
Both singular and infinite-order alternatives classify that entire language. -/
theorem unsafe_actual_binary_classification
    (PG : Paper1DirectGadgetAccepted) (PR : Paper1RestrictionAccepted)
    (PF : Paper1FactorClosureAccepted) (PU : Paper1UnaryAccepted)
    (PI : Paper1BinaryInterpolationAccepted) (L : Language)
    (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hunsafe : ¬ AllBinariesSafe L.family) :
    Tract (kImage L) ∨ Problem.SharpPHard .nativeX L := by
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
  obtain ⟨A, hA, hAL, hLA⟩ := PG.adjoin_equivalence PR L (binarySignature B)
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
  have hhard : Problem.SharpPHard .nativeX A := by
    by_cases hd : Matrix.det B = 0
    · obtain ⟨u, v, hu, hv, hfac⟩ := singular_binary_factorization B hB hd
      apply rankOne_binary_hard PF PU A hpreA (bothChargeSigns_not_commonOneSided hbothA)
        hnotA u v hu hv
      rwa [hfac]
    · have hinf : ¬ ProjectivelyFinite (transfer B) := hbad.resolve_left hd
      apply infinite_transfer_hard PI PF PU A hpreA hbothA hnotA B hmem _ hinf
      rw [transfer, Matrix.det_mul]
      exact mul_ne_zero hd det_X_ne_zero
  exact hhard.transport_unconditional hAL

end
end Paper2.HeightOne
