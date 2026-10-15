import Paper2.SourceFaithful.SourceStatements.PhaseProductParityRepresentatives
import Paper2.SourceFaithful.SourceStatements.PhaseProductParityBinary

/-! Source Proposition 5.13's original native-X contraction condition,
for the specified rotation/reflection representatives and both orientations.
All representative scales and the original Walsh coordinate transport remain
explicit; no whole-language safety statement is used. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable PhasePencil HeightOne HeightOne.Dihedral HeightOne.PhaseCards
open HeightOne.GroupSplit HeightOne.GroupSplit.MatrixGroup
open HeightOne.GroupSplit.FiniteGroupFacts.ProjectiveCentralizers

lemma BinaryPhase.scale_iff {N : ℕ} {ι : Type} [Fintype ι]
    (f : Tensor AlgebraicComplex ι) (c : AlgebraicComplex) (hc : c ≠ 0) :
    BinaryPhase N (c • f) ↔ BinaryPhase N f := by
  constructor
  · rintro ⟨hp,hr⟩
    exact ⟨(hasParity_scale_iff c hc f).mp hp,
      fun x => (RootComplement.smul_iff _ _ c hc).mp (hr x)⟩
  · intro hf
    exact hf.scale c

lemma analysis_transpose (B : AMat) :
    analysisKernel B.transpose = (analysisKernel B).transpose := by
  funext i j
  cases i <;> cases j <;>
    simp [analysisKernel,nativeKernel,walsh,X,Signature.disequality,Matrix.mul_apply] <;> ring

lemma transfer_of_reflected_walshBinary {B : AMat} {κ s : AlgebraicComplex}
    (hB : walshBinary B = κ • reflectedBinary s) :
    transfer B = (2 * κ) • ((zGL : AMat) * phase s) := by
  have hi : walshInv.transpose = walshInv := by
    funext i j
    cases i <;> cases j <;> rfl
  have hrec : B = walsh * walshBinary B * walsh := by
    rw [walshBinary,hi]
    simp only [← Matrix.mul_assoc,walsh_mul_walshInv,Matrix.one_mul]
    rw [Matrix.mul_assoc,walshInv_mul_walsh,Matrix.mul_one]
  rw [hrec,hB]
  funext i j
  cases i <;> cases j <;>
    simp [transfer,walsh,reflectedBinary,phase,balanced,zGL,diagonalGL,diagonal,
      X,Signature.disequality,Matrix.mul_apply,Matrix.smul_apply] <;> field_simp <;> ring

lemma reflected_analysis {B : AMat} {κ s : AlgebraicComplex}
    (hB : walshBinary B = κ • reflectedBinary s) :
    analysisKernel B.transpose = (-4 * κ) • minusKernel s ∧
      analysisKernel B = (-4 * κ) • reflectedBinary s := by
  have ht := reflection_reversed_analysis_kernel (transfer_of_reflected_walshBinary hB)
  have hn : -2 * (2 * κ) = -4 * κ := by ring
  rw [hn] at ht
  refine ⟨ht,?_⟩
  have h := congrArg Matrix.transpose ht
  rw [analysis_transpose,Matrix.transpose_transpose] at h
  have he : (minusKernel s).transpose = reflectedBinary s := by
    funext i j
    cases i <;> cases j <;> rfl
  simpa only [Matrix.transpose_smul,he] using h

lemma phase_analysis_transpose {B : AMat} {κ s : AlgebraicComplex}
    (hB : walshBinary B = κ • PhaseCards.plusKernel s) :
    analysisKernel B.transpose = (4 * κ) • PhaseCards.plusKernel s := by
  rw [analysis_transpose,rotation_analysis_kernel (CyclicDressing.transfer_of_walshBinary hB)]
  have he : (PhaseCards.plusKernel s).transpose = PhaseCards.plusKernel s := by
    funext i j
    cases i <;> cases j <;> rfl
  rw [Matrix.transpose_smul,he]
  congr 1
  ring

lemma card_scaled_kernel (c : AlgebraicComplex) (E : AMat)
    (i j : Fin 4) (hij : i ≠ j) (f : Signature AlgebraicComplex 4) :
    card (c • E) i j hij f = c • card E i j hij f := by
  unfold card
  exact contractKernel_scale c E _

def TwoKernelContractions (N : ℕ) (f : Signature AlgebraicComplex 4) : Prop :=
  ∀ (i j : Fin 4) (hij : i ≠ j) (s : AlgebraicComplex), Root N s →
    BinaryPhase N (card (PhaseCards.plusKernel s) i j hij f) ∧
      BinaryPhase N (card (minusKernel s) i j hij f)

theorem two_kernels_iff {N : ℕ} (hN : 0 < N) (f : Signature AlgebraicComplex 4) :
    TwoKernelContractions N f ↔ DihedralContractions N f := by
  constructor
  · intro h i j hij u v s hs
    have forward (v : Bool) (s : AlgebraicComplex) (hs : Root N s) :
        BinaryPhase N (card (xorKernel false v s) i j hij f) := by
      cases v
      · simpa only [xorKernel_false_false] using (h i j hij s hs).1
      · simpa only [xorKernel_false_true] using (h i j hij s hs).2
    cases u
    · exact forward v s hs
    · rw [xorKernel_reverse _ _ (root_ne_zero hN hs),card_scaled_kernel]
      have hi : Root N s⁻¹ := by change (s⁻¹)^N=1; rw [inv_pow,hs,inv_one]
      exact (forward (!v) s⁻¹ hi).scale (-s)
  · intro h i j hij s hs
    exact ⟨by simpa only [xorKernel_false_false] using h i j hij false false s hs,
      by simpa only [xorKernel_false_true] using h i j hij false true s hs⟩

def NativeDihedralContractions (N : ℕ)
    (P R : AlgebraicComplex → AMat) (f : Signature AlgebraicComplex 4) : Prop :=
  ∀ (i j : Fin 4) (hij : i ≠ j) (s : AlgebraicComplex), Root N s →
    BinaryPhase N (walshCoordinates (card (nativeKernel (P s)) i j hij f)) ∧
    BinaryPhase N (walshCoordinates (card (nativeKernel (P s).transpose) i j hij f)) ∧
    BinaryPhase N (walshCoordinates (card (nativeKernel (R s)) i j hij f)) ∧
    BinaryPhase N (walshCoordinates (card (nativeKernel (R s).transpose) i j hij f))

theorem native_dihedral_iff {N : ℕ} (hN : 0 < N)
    (P R : AlgebraicComplex → AMat) (κ τ : AlgebraicComplex → AlgebraicComplex)
    (hκ : ∀ s, Root N s → κ s ≠ 0) (hτ : ∀ s, Root N s → τ s ≠ 0)
    (hP : ∀ s, Root N s → walshBinary (P s) = κ s • PhaseCards.plusKernel s)
    (hR : ∀ s, Root N s → walshBinary (R s) = τ s • reflectedBinary s)
    (f : Signature AlgebraicComplex 4) :
    NativeDihedralContractions N P R f ↔ DihedralContractions N (walshCoordinates f) := by
  rw [← two_kernels_iff hN]
  constructor
  · intro h i j hij s hs
    have hp := (h i j hij s hs).1
    have hr := (h i j hij s hs).2.2.2
    rw [native_card_walsh,representative_card (hP s hs)] at hp
    rw [native_card_walsh,(reflected_analysis (hR s hs)).1,card_scaled_kernel] at hr
    exact ⟨by
      rw [← card_plus] at hp
      exact (BinaryPhase.scale_iff _ _ (mul_ne_zero (by norm_num) (hκ s hs))).mp hp,
      (BinaryPhase.scale_iff _ _ (mul_ne_zero (by norm_num) (hτ s hs))).mp hr⟩
  · intro h i j hij s hs
    have ht := (two_kernels_iff hN (walshCoordinates f)).mp h
    have hp := (h i j hij s hs).1
    have hm := (h i j hij s hs).2
    have hr : BinaryPhase N (card (reflectedBinary s) i j hij (walshCoordinates f)) := by
      have he : xorKernel true false s = reflectedBinary s := by
        funext a b; cases a <;> cases b <;> rfl
      simpa only [he] using ht i j hij true false s hs
    refine ⟨?_,?_,?_,?_⟩
    · rw [native_card_walsh,representative_card (hP s hs),← card_plus]
      exact hp.scale _
    · rw [native_card_walsh,phase_analysis_transpose (hP s hs),card_scaled_kernel]
      exact hp.scale _
    · rw [native_card_walsh,(reflected_analysis (hR s hs)).2,card_scaled_kernel]
      exact hr.scale _
    · rw [native_card_walsh,(reflected_analysis (hR s hs)).1,card_scaled_kernel]
      exact hm.scale _

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity
