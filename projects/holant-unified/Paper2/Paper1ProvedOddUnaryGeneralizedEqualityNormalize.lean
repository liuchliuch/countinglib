import Paper2.RelativeEO.GeneralizedEqualityGadget
import Paper2.Tractable.Conformal
import Paper2.SourceFaithful.GadgetAugmentation
import Paper2.Paper1ProvedNormalizationProvider
import Paper2.Paper1ProvedGadgetProvider
import Paper2.Paper1ProvedRestrictionProvider
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Genuine diagonal normalization of a realized weighted generalized equality.
The finite language retains exact unit equality and both exact unit pins. Each
augmentation uses a real native-X network with its nonzero scalar, and the global
basis change uses the actual canonical controlled normalization provider. This
module makes no classification assumption about a degree-restricted CSP. -/
namespace Paper2.Paper1Proved.OddUnary.GeneralizedEqualityNormalize
open Tractable ExactInput SourceFaithful
noncomputable section

/-- The literal equality table, with its original ordered ports. -/
def equality (n : ℕ) : Signature AlgebraicComplex n :=
  Paper2.RelativeEO.generalizedEquality 1 1

/-- A diagonal chart whose disequality multiplier is its first entry. -/
def diagonal (t : AlgebraicComplex) (ht : t ≠ 0) : InvertibleKernel where
  matrix := diagonalKernel t 1
  inverse := diagonalKernel t⁻¹ 1
  matrix_inverse := by
    funext a b
    cases a <;> cases b <;>
      simp [Kernel.mul_apply,diagonalKernel,Signature.equality,ht]
  inverse_matrix := by
    funext a b
    cases a <;> cases b <;>
      simp [Kernel.mul_apply,diagonalKernel,Signature.equality,ht]

theorem diagonal_conformal (t : AlgebraicComplex) (ht : t ≠ 0) :
    XConformal (diagonal t ht) := by
  refine ⟨t,ht,?_⟩
  funext a b
  cases a <;> cases b <;>
    simp [Kernel.pullback,Kernel.mul_apply,Kernel.transpose,diagonal,
      diagonalKernel,Signature.disequality]

/-- Root extraction stays in the algebraic-complex field. -/
theorem root (n : ℕ) (hn : 0 < n) (a b : AlgebraicComplex) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ t : AlgebraicComplex, t ≠ 0 ∧ t ^ n * a = b := by
  obtain ⟨t,ht⟩ := @IsAlgClosed.exists_pow_nat_eq AlgebraicComplex _
    (IsAlgClosure.isAlgClosed ℚ) (b/a) n hn
  refine ⟨t,?_,?_⟩
  · intro hz
    apply div_ne_zero hb ha
    rw [← ht,hz]
    simp [hn.ne']
  · rw [ht]
    exact div_mul_cancel₀ b ha

theorem diagonal_equality (n : ℕ) (hn : 0 < n) (t : AlgebraicComplex) (ht : t ≠ 0)
    (a b : AlgebraicComplex) (h : t ^ n * a = b) :
    (diagonal t ht).action (Paper2.RelativeEO.generalizedEquality (n := n) a b) = b • equality n := by
  classical
  change Signature.coordinateAction (fun _ => diagonalKernel t 1) _ = _
  rw [coordinateAction_diagonal]
  have hwords : (fun _ : Fin n => false) ≠ (fun _ => true) := by
    intro he
    exact Bool.false_ne_true (congrFun he ⟨0,hn⟩)
  funext x
  by_cases h0 : x = (fun _ => false)
  · subst x
    simp [Paper2.RelativeEO.generalizedEquality,equality,diagonalCoefficient,h,hwords]
  · by_cases h1 : x = (fun _ => true)
    · subst x
      simp [Paper2.RelativeEO.generalizedEquality,equality,diagonalCoefficient,h0]
    · simp [Paper2.RelativeEO.generalizedEquality,equality,h0,h1]

theorem diagonal_pin (t : AlgebraicComplex) (ht : t ≠ 0) (b : Bool) :
    (diagonal t ht).action (TensorDecomposition.literalPin b) =
      (if b then 1 else t) • TensorDecomposition.literalPin b := by
  classical
  change Signature.coordinateAction (fun _ => diagonalKernel t 1) _ = _
  rw [coordinateAction_diagonal]
  funext x
  have hx : x = (fun _ => x 0) := by funext i; rw [Fin.eq_zero i]
  rw [hx]
  cases b <;> cases x 0 <;>
    simp [diagonalCoefficient,TensorDecomposition.literalPin]

theorem equality_ne_zero (n : ℕ) : equality n ≠ 0 := by
  classical
  intro h
  have he := congrFun h (fun _ => false)
  simp [equality,Paper2.RelativeEO.generalizedEquality] at he
  split_ifs at he <;> norm_num at he

/-- A supplied nonzero scalar multiple is a genuine projective network receipt. -/
theorem unscale_mem (F : SignatureFamily AlgebraicComplex) {n : ℕ}
    (f : Signature AlgebraicComplex n) (c : AlgebraicComplex) (hc : c ≠ 0)
    (hm : (⟨n,c • f⟩ : AnySignature AlgebraicComplex) ∈ F) :
    NativeNetworkRealizesUpTo F f := by
  obtain ⟨N,hU,hX,s,hs,hN⟩ := NativeNetworkRealizesUpTo.of_mem hm
  refine ⟨N,hU,hX,s*c,mul_ne_zero hs hc,?_⟩
  funext x
  simpa only [Pi.smul_apply,smul_eq_mul,mul_assoc] using congrFun hN x

/-- Weighted equality plus actual native pins has an equivalent normalized
finite presentation retaining literal equality and both literal unit pins. -/
theorem normalized (L : Language) (hpre : Preprocessed L.family) {n : ℕ}
    (hn : 0 < n) (a b : AlgebraicComplex) (ha : a ≠ 0) (hb : b ≠ 0)
    (hgraph : NativeNetworkRealizesUpTo L.family (Paper2.RelativeEO.generalizedEquality (n := n) a b))
    (h0 : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (h1 : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ t : AlgebraicComplex, ∃ ht : t ≠ 0, ∃ M : Language,
      t ^ n * a = b ∧ familyAction (diagonal t ht) L.family ⊆ M.family ∧
      (⟨n,equality n⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      Preprocessed M.family ∧
      (Tract (Paper2.kImage M) → Tract (Paper2.kImage L)) ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  classical
  obtain ⟨t,ht,he⟩ := root n hn a b ha hb
  let D := diagonal t ht
  have hf : Paper2.RelativeEO.generalizedEquality (n := n) a b ≠ 0 := by
    intro hf
    have hh := congrArg D.action hf
    rw [diagonal_equality n hn t ht a b he] at hh
    have hz := Signature.coordinateAction_zero (K := AlgebraicComplex) (fun _ : Fin n => D.matrix)
    change b • equality n = Signature.coordinateAction (fun _ => D.matrix) 0 at hh
    rw [hz] at hh
    exact equality_ne_zero n ((smul_eq_zero.mp hh).resolve_left hb)
  obtain ⟨A,hA,hAL,hLA⟩ := directGadgetProvider.adjoin_equivalence restrictionProvider L
    (Paper2.RelativeEO.generalizedEquality (n := n) a b) hgraph
  have hsub : L.family ⊆ A.family := by rw [hA]; exact Set.subset_insert _ _
  have hpA : Preprocessed A.family := by
    rw [hA]
    rintro f (rfl | hfA)
    · exact ⟨hn,hf⟩
    · exact hpre f hfA
  obtain ⟨B,hB,hBA,hAB⟩ := normalizationProvider.normalize A hpA D (diagonal_conformal t ht)
  have hpB : Preprocessed B.family := by
    rw [hB]
    exact Conformal.preprocessed_familyAction D hpA
  have hEq : (⟨n,b • equality n⟩ : AnySignature AlgebraicComplex) ∈ B.family := by
    rw [hB]
    refine ⟨⟨n,Paper2.RelativeEO.generalizedEquality (n := n) a b⟩,?_,?_⟩
    · rw [hA]; exact Or.inl rfl
    · simp only [D,diagonal_equality n hn t ht a b he]
  obtain ⟨C,hC,hCB,hBC⟩ := directGadgetProvider.adjoin_equivalence restrictionProvider B
    (equality n) (unscale_mem B.family _ b hb hEq)
  have hBCsub : B.family ⊆ C.family := by rw [hC]; exact Set.subset_insert _ _
  have hPin (u : Bool) : NativeNetworkRealizesUpTo C.family (TensorDecomposition.literalPin u) := by
    apply unscale_mem C.family _ (if u then 1 else t) (by cases u <;> simp_all)
    apply hBCsub
    rw [hB]
    refine ⟨⟨1,TensorDecomposition.literalPin u⟩,?_,?_⟩
    · apply hsub
      cases u <;> assumption
    · simp only [D,diagonal_pin]
  obtain ⟨M,hM,hMC⟩ := directGadgetProvider.adjoin_pair C
    (TensorDecomposition.literalPin false) (TensorDecomposition.literalPin true) (hPin false) (hPin true)
  have hCM : C.family ⊆ M.family := by
    rw [hM]
    intro f hfC
    exact Or.inr (Or.inr hfC)
  have hpC : Preprocessed C.family := by
    rw [hC]
    rintro f (rfl | hfB)
    · exact ⟨hn,equality_ne_zero n⟩
    · exact hpB f hfB
  refine ⟨t,ht,M,he,?_,?_,?_,?_,?_,?_,hMC.trans (hCB.trans (hBA.trans hAL)),
    hLA.trans (hAB.trans (hBC.trans (restrictionProvider.restriction_2_5 C M hCM)))⟩
  · exact (familyAction_mono D hsub).trans (by rw [← hB]; exact hBCsub.trans hCM)
  · apply hCM
    rw [hC]
    exact Or.inl rfl
  · rw [hM]; exact Or.inl rfl
  · rw [hM]; exact Or.inr (Or.inl rfl)
  · rw [hM]
    rintro f (rfl | rfl | hfC)
    · exact ⟨by decide,TensorDecomposition.literalPin_ne_zero false⟩
    · exact ⟨by decide,TensorDecomposition.literalPin_ne_zero true⟩
    · exact hpC f hfC
  · intro htract
    have hbtract := htract.mono_family (familyAction_mono sourceKBasis (hBCsub.trans hCM))
    have hatract : Tract (Paper2.kImage A) := by
      apply (xConformal_tract_iff (diagonal_conformal t ht) A.family).mpr
      simpa only [Paper2.kImage,hB] using hbtract
    exact hatract.mono_family (familyAction_mono sourceKBasis hsub)

end
end Paper2.Paper1Proved.OddUnary.GeneralizedEqualityNormalize
