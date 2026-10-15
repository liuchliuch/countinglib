import Paper2.HeightOne.Dihedral.Quaternary
import Paper2.HeightOne.PhaseCards.Source

/-! Actual binary group membership forces the precise complementary-entry
phase relation needed by every ordered four-port RN pencil. -/
namespace Paper2.HeightOne.Dihedral
noncomputable section
open Tractable PhasePencil PhaseCards GroupSplit GroupSplit.MatrixGroup

/-- Zero is retained, and a live pair has a negative root ratio. -/
def RootComplement (N : ℕ) (a b : AlgebraicComplex) : Prop :=
  (a = 0 ∧ b = 0) ∨ ∃ r, Root N r ∧ a ≠ 0 ∧ b = -r * a

lemma root_of_unity {N : ℕ} (s : rootsOfUnity N AlgebraicComplex) :
    Root N (s.val : AlgebraicComplex) := by
  have h := s.property
  rw [mem_rootsOfUnity] at h
  exact congrArg (fun z : AlgebraicComplexˣ => (z : AlgebraicComplex)) h

lemma RootComplement.smul_iff {N : ℕ} (a b c : AlgebraicComplex) (hc : c ≠ 0) :
    RootComplement N (c * a) (c * b) ↔ RootComplement N a b := by
  constructor
  · rintro (⟨ha,hb⟩ | ⟨r,hr,ha,hb⟩)
    · exact Or.inl ⟨(mul_eq_zero.mp ha).resolve_left hc, (mul_eq_zero.mp hb).resolve_left hc⟩
    · refine Or.inr ⟨r,hr,(mul_ne_zero_iff.mp ha).2,?_⟩
      apply mul_left_cancel₀ hc
      linear_combination hb
  · rintro (⟨rfl,rfl⟩ | ⟨r,hr,ha,hb⟩)
    · exact Or.inl ⟨mul_zero _,mul_zero _⟩
    · exact Or.inr ⟨r,hr,mul_ne_zero hc ha,by rw [hb]; ring⟩

lemma plusKernel_rootComplement {N : ℕ} (hN : 0 < N) (s : AlgebraicComplex)
    (hs : Root N s) (a b : Bool) :
    RootComplement N (plusKernel s a b) (plusKernel s (!a) (!b)) := by
  have hs0 := root_ne_zero hN hs
  cases a <;> cases b
  · exact Or.inr ⟨s,hs,one_ne_zero,by simp [plusKernel]⟩
  · exact Or.inl ⟨by simp [plusKernel],by simp [plusKernel]⟩
  · exact Or.inl ⟨by simp [plusKernel],by simp [plusKernel]⟩
  · refine Or.inr ⟨1 / s,root_div (by simp [Root]) hs,by simp [plusKernel, hs0],?_⟩
    simp [plusKernel, hs0]

lemma reflectedBinary_rootComplement {N : ℕ} (hN : 0 < N) (s : AlgebraicComplex)
    (hs : Root N s) (a b : Bool) :
    RootComplement N (reflectedBinary s a b) (reflectedBinary s (!a) (!b)) := by
  have hs0 := root_ne_zero hN hs
  cases a <;> cases b
  · exact Or.inl ⟨by simp [reflectedBinary],by simp [reflectedBinary]⟩
  · refine Or.inr ⟨1 / s,root_div (by simp [Root]) hs,by simp [reflectedBinary, hs0],?_⟩
    simp [reflectedBinary, hs0]
  · exact Or.inr ⟨s,hs,one_ne_zero,by simp [reflectedBinary]⟩
  · exact Or.inl ⟨by simp [reflectedBinary],by simp [reflectedBinary]⟩

theorem actual_binary_rootComplement {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hN : 0 < N) (hG : actualClasses F = dihedralPhaseClasses N)
    (hsafe : AllBinariesSafe F) (f : Signature AlgebraicComplex 2)
    (hf : NetworkRealizable F f) (x : Fin 2 → Bool) :
    RootComplement N (walshCoordinates f x) (walshCoordinates f (fun j => !(x j))) := by
  by_cases hz : f = 0
  · rw [hz,walsh_zero]
    exact Or.inl ⟨rfl,rfl⟩
  have hB := actual_tableBinary hsafe f hf hz
  have he := binarySignature_tableBinary f
  rw [← he,walshCoordinates_binary]
  rcases actual_binary_phase_shape (Or.inr hG) hB with ⟨s,c,hc,hs⟩ | ⟨s,c,hc,hs⟩
  · rw [rotation_walsh_binary hs]
    change RootComplement N ((c/2) * plusKernel (s.val : AlgebraicComplex) (x 0) (x 1))
      ((c/2) * plusKernel (s.val : AlgebraicComplex) (!(x 0)) (!(x 1)))
    exact (RootComplement.smul_iff _ _ _ (div_ne_zero hc (by norm_num))).mpr
      (plusKernel_rootComplement hN _ (root_of_unity s) _ _)
  · rw [reflection_walsh_binary hs]
    change RootComplement N ((c/2) * reflectedBinary (s.val : AlgebraicComplex) (x 0) (x 1))
      ((c/2) * reflectedBinary (s.val : AlgebraicComplex) (!(x 0)) (!(x 1)))
    exact (RootComplement.smul_iff _ _ _ (div_ne_zero hc (by norm_num))).mpr
      (reflectedBinary_rootComplement hN _ (root_of_unity s) _ _)

end
end Paper2.HeightOne.Dihedral

