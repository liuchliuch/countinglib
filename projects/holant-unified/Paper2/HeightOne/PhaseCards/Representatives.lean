import Paper2.HeightOne.PhaseCards.Kernels

/-! Actual ordered binary representatives of the complete normalized class set.
The scalars are retained rather than treating projective matrices as gadgets. -/
namespace Paper2.HeightOne.PhaseCards
open Tractable GroupSplit GroupSplit.MatrixGroup
open GroupSplit.FiniteGroupFacts.ProjectiveCentralizers
noncomputable section

lemma actual_rotation {F : SignatureFamily AlgebraicComplex}
    {s : AlgebraicComplexˣ} (hs : phaseHom s ∈ actualClasses F) :
    ∃ (B : AMat) (c : AlgebraicComplex),
      ActualNonsingular F B ∧ c ≠ 0 ∧ transfer B = c • phase s := by
  obtain ⟨B, hB, hp⟩ := actualClass_representative hs
  change projectiveClass (transfer B) = pglToProjectiveClass (pglMk _ (phaseGL s)) at hp
  rw [pglToProjectiveClass_mk] at hp
  obtain ⟨c, hc, he⟩ := projectiveClass_eq_iff.mp hp
  exact ⟨B, c, hB, hc, he⟩

lemma actual_reflection {F : SignatureFamily AlgebraicComplex}
    {s : AlgebraicComplexˣ} (hs : zClass * phaseHom s ∈ actualClasses F) :
    ∃ (B : AMat) (c : AlgebraicComplex),
      ActualNonsingular F B ∧ c ≠ 0 ∧ transfer B = c • ((zGL : AMat) * phase s) := by
  obtain ⟨B, hB, hp⟩ := actualClass_representative hs
  change projectiveClass (transfer B) =
    pglToProjectiveClass (pglMk _ zGL * pglMk _ (phaseGL s)) at hp
  rw [← map_mul, pglToProjectiveClass_mk] at hp
  obtain ⟨c, hc, he⟩ := projectiveClass_eq_iff.mp hp
  exact ⟨B, c, hB, hc, he⟩

/-- Every root phase has a genuine binary contraction card in either complete
normalized group. Its Walsh kernel includes the literal factor two. -/
theorem actual_plus_card {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hG : actualClasses F = cyclicPhaseClasses N ∨
      actualClasses F = dihedralPhaseClasses N)
    (s : rootsOfUnity N AlgebraicComplex) :
    ∃ (B : AMat) (c : AlgebraicComplex),
      ActualNonsingular F B ∧ c ≠ 0 ∧
      analysisKernel B = (2 * c) • plusKernel s.val := by
  have hs : phaseHom s.val ∈ actualClasses F := by
    rcases hG with hG | hG
    · rw [hG]; exact ⟨s.val, s.property, rfl⟩
    · rw [hG]; exact Or.inl ⟨s.val, s.property, rfl⟩
  obtain ⟨B, c, hB, hc, ht⟩ := actual_rotation hs
  exact ⟨B, c, hB, hc, rotation_analysis_kernel ht⟩

/-- Every reflected root phase has an actual reversed binary card. The ordered
reversal is an actual boundary permutation and its scale is exactly -2c. -/
theorem actual_minus_card {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hG : actualClasses F = dihedralPhaseClasses N)
    (s : rootsOfUnity N AlgebraicComplex) :
    ∃ (B : AMat) (c : AlgebraicComplex),
      ActualNonsingular F B ∧ c ≠ 0 ∧
      analysisKernel B = (-2 * c) • minusKernel s.val := by
  have hs : zClass * phaseHom s.val ∈ actualClasses F := by
    rw [hG]
    exact Or.inr ⟨phaseHom s.val, ⟨s.val, s.property, rfl⟩, rfl⟩
  obtain ⟨B, c, hB, hc, ht⟩ := actual_reflection hs
  exact ⟨B.transpose, c, actualNonsingular_transpose hB, hc,
    reflection_reversed_analysis_kernel ht⟩

end
end Paper2.HeightOne.PhaseCards
