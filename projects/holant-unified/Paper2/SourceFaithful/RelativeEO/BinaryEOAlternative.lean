import Paper2.SourceFaithful.OccurrenceInputs
import Paper2.SourceFaithful.UnaryExit
import Paper2.RelativeEO.ARSMatching

/-! Exact binary relative EO alternative in canonical fixed-field output
semantics. The only accepted inputs are source Paper 1 interpolation, factor
extraction and unary classification. Algebraic phase arithmetic is reused. -/
namespace Paper2.SourceFaithful.RelativeEO
open Tractable ExactInput Paper2.RelativeEO
open HeightOne.GroupSplit HeightOne.GroupSplit.MatrixGroup

/-- The source interpolation plus actual prime-factor extraction closes the
infinite-order branch for the whole retained ambient language. -/
theorem infinite_transfer_hard (P : Paper1BinaryInterpolationAccepted)
    (F : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted) (L : Language)
    (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (B : Binary (K := AlgebraicComplex))
    (hB : (⟨2, matrixSignature B⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hdet : Matrix.det (transfer B) ≠ 0) (hinf : ¬ ProjectivelyFinite (transfer B)) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨u, v, M, hu, hv, hM, hML⟩ := P.infiniteOrder_3_1 L hpre hboth B hB hdet hinf
  have hLM : L.family ⊆ M.family := by rw [hM]; exact Set.subset_insert _ _
  have hpreM : Preprocessed M.family := by
    intro g hg
    rw [hM] at hg
    rcases hg with rfl | hg
    · exact ⟨by change 0 < (2 : ℕ); decide, ordered_tensor_ne_zero u v hu hv⟩
    · exact hpre g hg
  have htwoM : ¬ CommonOneSided M.family := by
    intro hs
    have hL := hs.mono_family hLM
    obtain ⟨⟨f, hf, x, hx, hneg⟩, ⟨g, hg, y, hy, hpos⟩⟩ := hboth
    rcases hL with hL | hL
    · exact (not_le_of_gt hneg) (hL f hf x hx)
    · exact (not_le_of_gt hpos) (hL g hg y hy)
  have hnotM : ¬ Tract (kImage M) :=
    fun ht => hnot (ht.mono_family (familyAction_mono sourceKBasis hLM))
  have hmem : (⟨2, Signature.tensor u v⟩ : AnySignature AlgebraicComplex) ∈ M.family := by
    rw [hM]
    exact Set.mem_insert _ _
  exact (rankOne_binary_hard F U M hpreM htwoM hnotM u v hu hv hmem).transport hML


theorem binary_eo_alternative (P : Paper1BinaryInterpolationAccepted)
    (F : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted) (L : Language)
    (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (f : Signature AlgebraicComplex 2)
    (hf : f ≠ 0) (hEO : Signature.CentralSupport f)
    (hmem : (⟨2, f⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ProjectiveARS f ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  let a := f (binWord false true)
  let b := f (binWord true false)
  have hform : f = eoSignature a b := binary_central_form f hEO
  have hside : ¬ CommonOneSided L.family := by
    intro hs
    obtain ⟨⟨g, hg, x, hx, hneg⟩, ⟨h, hh, y, hy, hpos⟩⟩ := hboth
    rcases hs with hs | hs
    · exact (not_le_of_gt hneg) (hs g hg x hx)
    · exact (not_le_of_gt hpos) (hs h hh y hy)
  have heomem : (⟨2, eoSignature a b⟩ : AnySignature AlgebraicComplex) ∈ L.family := hform ▸ hmem
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      apply hf
      rw [hform, ha, hb, eoSignature_zero]
    right
    have hfactor : (⟨2, Signature.tensor (pinAmplitude true b) (TensorDecomposition.literalPin false)⟩ :
        AnySignature AlgebraicComplex) ∈ L.family := by
      simpa only [ha, eoSignature_left_zero] using heomem
    exact rankOne_binary_hard F U L hpre hside hnot _ _ (pinAmplitude_ne_zero true b hb)
      (TensorDecomposition.literalPin_ne_zero false) hfactor
  · by_cases hb : b = 0
    · right
      have hfactor : (⟨2, Signature.tensor (pinAmplitude false a) (TensorDecomposition.literalPin true)⟩ :
          AnySignature AlgebraicComplex) ∈ L.family := by
        simpa only [hb, eoSignature_right_zero] using heomem
      exact rankOne_binary_hard F U L hpre hside hnot _ _ (pinAmplitude_ne_zero false a ha)
        (TensorDecomposition.literalPin_ne_zero true) hfactor
    · by_cases hfinite : ProjectivelyFinite (transfer (eoMatrix a b))
      · left
        rw [hform]
        exact eo_finite_order_ars a b ha hb hfinite
      · right
        apply infinite_transfer_hard P F U L hpre hboth hnot (eoMatrix a b) heomem _ hfinite
        rw [eo_transfer, Matrix.det_diagonal]
        simpa [Fintype.prod_bool] using mul_ne_zero hb ha


/-- The source relative terminal is fully proved for an arity-two EO member,
using only the exact cited Paper 1 interpolation/factor/unary inputs. -/
theorem binary_relative_terminal (P : Paper1BinaryInterpolationAccepted)
    (F : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted) (L : Language)
    (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (f : Signature AlgebraicComplex 2)
    (hf : f ≠ 0) (hEO : Signature.CentralSupport f)
    (hmem : (⟨2,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hout : ¬ IsARSProduct f) : FixedFieldOutput.SharpPHard .nativeX L := by
  rcases binary_eo_alternative P F U L hpre hboth hnot f hf hEO hmem with hs | hh
  · exact False.elim (hout (binary_arsProduct f hf hEO hs))
  · exact hh


end Paper2.SourceFaithful.RelativeEO
