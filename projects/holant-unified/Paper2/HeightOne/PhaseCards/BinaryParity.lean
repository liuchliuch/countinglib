import Paper2.HeightOne.PhaseCards.WalshTransport

/-! The arity-two case of source Lemma 5.10, from membership in the complete
actual transfer group and literal Walsh matrix identities. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable GroupSplit GroupSplit.MatrixGroup
open GroupSplit.FiniteGroupFacts.ProjectiveCentralizers

lemma walshCoordinates_binary (B : AMat) :
    walshCoordinates (binarySignature B) = binarySignature (walshBinary B) :=
  by
    calc
      _ = Signature.coordinateAction (fun _ => walshInv) (binarySignature B) := by
        classical
        funext x
        unfold walshCoordinates action Signature.coordinateAction
        exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)
      _ = _ := coordinateAction_kernelSignature walshInv B

lemma binarySignature_reindex (B : AMat) :
    binarySignature B = Tensor.reindex finTwoEquiv.symm (kernelTensor B) := rfl

lemma binary_diagonal_signature_even (B : AMat)
    (h01 : B false true = 0) (h10 : B true false = 0) :
    SupportedOnParity (binarySignature B) 0 := by
  rw [binarySignature_reindex]
  exact supportedOnParity_reindex _ _ _ (binary_diagonal_even B h01 h10)

lemma binary_antidiagonal_signature_odd (B : AMat)
    (h00 : B false false = 0) (h11 : B true true = 0) :
    SupportedOnParity (binarySignature B) 1 := by
  rw [binarySignature_reindex]
  exact supportedOnParity_reindex _ _ _ (binary_antidiagonal_odd B h00 h11)

lemma rotation_binary_even {B : AMat} {c s : AlgebraicComplex}
    (hB : transfer B = c • phase s) :
    SupportedOnParity (walshCoordinates (binarySignature B)) 0 := by
  rw [walshCoordinates_binary, rotation_walsh_binary hB]
  apply binary_diagonal_signature_even <;> simp [plusKernel]

lemma reflection_binary_odd {B : AMat} {c s : AlgebraicComplex}
    (hB : transfer B = c • ((zGL : AMat) * phase s)) :
    SupportedOnParity (walshCoordinates (binarySignature B)) 1 := by
  rw [walshCoordinates_binary, reflection_walsh_binary hB]
  apply binary_antidiagonal_signature_odd <;> simp [reflectedBinary]

lemma actual_transfer_GL {F : SignatureFamily AlgebraicComplex} {B : AMat}
    (hB : ActualNonsingular F B) :
    ∃ U : Matrix.GeneralLinearGroup Bool AlgebraicComplex,
      (U : AMat) = transfer B ∧ pglMk _ U ∈ actualClasses F := by
  have hd : Matrix.det (transfer B) ≠ 0 := by
    rw [transfer, Matrix.det_mul]
    exact mul_ne_zero hB.2 det_X_ne_zero
  let U := Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer B) hd
  exact ⟨U, rfl, U, ⟨B, hB, 1, one_ne_zero, (one_smul _ _).symm⟩, rfl⟩

lemma actual_binary_phase_shape {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hG : actualClasses F = cyclicPhaseClasses N ∨
      actualClasses F = dihedralPhaseClasses N) {B : AMat} (hB : ActualNonsingular F B) :
    (∃ (s : rootsOfUnity N AlgebraicComplex) (c : AlgebraicComplex),
      c ≠ 0 ∧ transfer B = c • phase s.val) ∨
    (∃ (s : rootsOfUnity N AlgebraicComplex) (c : AlgebraicComplex),
      c ≠ 0 ∧ transfer B = c • ((zGL : AMat) * phase s.val)) := by
  obtain ⟨U, hU, hu⟩ := actual_transfer_GL hB
  have hrot (h : pglMk _ U ∈ cyclicPhaseClasses N) :
      ∃ (s : rootsOfUnity N AlgebraicComplex) (c : AlgebraicComplex),
        c ≠ 0 ∧ transfer B = c • phase s.val := by
    obtain ⟨s, hs, he⟩ := h
    have he' := pglMk_eq_iff_projectiveClass_eq.mp he.symm
    rw [hU] at he'
    obtain ⟨c, hc, hm⟩ := projectiveClass_eq_iff.mp he'
    exact ⟨⟨s, hs⟩, c, hc, hm⟩
  rcases hG with hG | hG
  · left; exact hrot (hG ▸ hu)
  · rw [hG] at hu
    rcases hu with hr | ⟨q, ⟨s, hs, rfl⟩, he⟩
    · exact Or.inl (hrot hr)
    · right
      change pglMk _ zGL * pglMk _ (phaseGL s) = pglMk _ U at he
      rw [← map_mul] at he
      have he' := pglMk_eq_iff_projectiveClass_eq.mp he.symm
      rw [hU] at he'
      obtain ⟨c, hc, hm⟩ := projectiveClass_eq_iff.mp he'
      exact ⟨⟨s, hs⟩, c, hc, hm⟩

theorem normalized_binary_hasParity {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hG : actualClasses F = cyclicPhaseClasses N ∨
      actualClasses F = dihedralPhaseClasses N) {B : AMat} (hB : ActualNonsingular F B) :
    HasParity (walshCoordinates (binarySignature B)) := by
  rcases actual_binary_phase_shape hG hB with ⟨s, c, hc, ht⟩ | ⟨s, c, hc, ht⟩
  · exact supportedOnParity_hasParity (rotation_binary_even ht)
  · exact supportedOnParity_hasParity (reflection_binary_odd ht)

theorem cyclic_binary_even {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hG : actualClasses F = cyclicPhaseClasses N) {B : AMat} (hB : ActualNonsingular F B) :
    SupportedOnParity (walshCoordinates (binarySignature B)) 0 := by
  obtain ⟨U, hU, hu⟩ := actual_transfer_GL hB
  rw [hG] at hu
  obtain ⟨s, hs, he⟩ := hu
  have he' := pglMk_eq_iff_projectiveClass_eq.mp he.symm
  rw [hU] at he'
  obtain ⟨c, hc, hm⟩ := projectiveClass_eq_iff.mp he'
  exact rotation_binary_even hm

end
end Paper2.HeightOne.PhaseCards
