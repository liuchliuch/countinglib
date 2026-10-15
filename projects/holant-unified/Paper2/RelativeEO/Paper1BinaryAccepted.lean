import Paper2.RelativeEO.BinaryEOArithmetic
import Paper2.RelativeEO.RankOneExit

/-! Exact infinite-projective-order clause of official Paper 1 Lemma 3.1,
restated in Paper 2 Lemma 3.1 (source lines 2004–2019). The conclusion is a
retained literal augmentation by an actual nonzero rank-one binary, together
with a genuine length-controlled oracle reduction. Unary hardness is proved
from factors separately; no Paper 2 EO alternative is an accepted field. -/
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup

structure Paper1BinaryInterpolationAccepted where
  infiniteOrder_3_1 : ∀ (L : Language), Preprocessed L.family → BothChargeSigns L.family →
    ∀ B : Binary (K := AlgebraicComplex),
      (⟨2, matrixSignature B⟩ : AnySignature AlgebraicComplex) ∈ L.family →
      Matrix.det (transfer B) ≠ 0 → ¬ ProjectivelyFinite (transfer B) →
      ∃ (u v : Signature AlgebraicComplex 1) (M : Language), u ≠ 0 ∧ v ≠ 0 ∧
        M.family = insert (⟨2, Signature.tensor u v⟩ : AnySignature AlgebraicComplex) L.family ∧
        Reduces .nativeX M L

/-- The source interpolation plus actual prime-factor extraction closes the
infinite-order branch for the whole retained ambient language. -/
theorem infinite_transfer_hard (P : Paper1BinaryInterpolationAccepted)
    (F : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted) (L : Language)
    (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (B : Binary (K := AlgebraicComplex))
    (hB : (⟨2, matrixSignature B⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hdet : Matrix.det (transfer B) ≠ 0) (hinf : ¬ ProjectivelyFinite (transfer B)) :
    SharpPHard .nativeX L := by
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
  exact (rankOne_binary_hard F U M hpreM htwoM hnotM u v hu hv hmem).transport_unconditional hML

end Paper2.RelativeEO
