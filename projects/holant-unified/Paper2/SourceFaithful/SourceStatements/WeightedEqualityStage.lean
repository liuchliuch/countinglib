import Paper2.HeightOne.GroupSplit.Source
import Paper2.HeightOne.GroupSplit.Paper1Proved
import Paper2.HeightTwo.Normalization
import Paper2.Paper1ProvedGadgetProvider
import Paper2.Paper1ProvedRestrictionProvider
import Paper2.SourceFaithful.SourceStatements.PublicReduction

/-! Source Theorem 5.4's weighted-equality membership convention.  The equality
is adjoined to an actual finite language by the proved graph compiler, and
both reductions use the strict public output convention.  No available
factor, basis, preprocessing or accepted-provider premise is supplied. -/
namespace Paper2.SourceFaithful.SourceStatements.WeightedEqualityStage
open Paper2.Tractable Paper2.ExactInput Paper2.Paper1Proved
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The first alternative occurs in this genuine finite equivalent stage.
The exact inserted signature is a nonsingular diagonal weighted equality. -/
def ContainsInEquivalentStage (L : Language) : Prop :=
  ∃ (M : Language) (p q : AlgebraicComplex), p ≠ 0 ∧ q ≠ 0 ∧
    M.family = insert (⟨2,kernelSignature (diagonalKernel p q)⟩ :
      AnySignature AlgebraicComplex) L.family ∧
    (⟨2,kernelSignature (diagonalKernel p q)⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
    L.family ⊆ M.family ∧
    Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M

/-- Install the actual ordered graph witness, keeping every original row,
including zero and nullary rows. The back reduction executes the graph
substitution and the answer converters; restriction gives the other direction. -/
theorem adjoin_weighted_equality (L : Language) (h : WeightedEqualityReachable L.family) :
    ContainsInEquivalentStage L := by
  obtain ⟨f,hf,hweighted⟩ := h
  obtain ⟨M,hM,hback⟩ := directGadgetProvider.adjoin_realizable L f hf
  have hforward : L.family ⊆ M.family := by
    rw [hM]
    exact Set.subset_insert _ _
  have htable := HeightTwo.weightedEquality_table f hweighted
  rw [htable] at hM
  refine ⟨M,f ![false,false],f ![true,true],hweighted.2.2.1,hweighted.2.2.2,hM,?_,
    hforward,PublicReduction.of_fixed_field .nativeX M L hback,
    PublicReduction.of_fixed_field .nativeX L M (restriction L M hforward)⟩
  rw [hM]
  exact Set.mem_insert _ _

/-- Source Theorem 5.4 with the actual current-set first alternative and the
complete original odd normalized transfer group in the second alternative.
The two finite-group inputs are instantiated by their proved source modules. -/
theorem theorem_5_4 (L : Language) (B : AMat)
    (hBmem : (⟨2,binarySignature B⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hB : IsMountain (d:=1) (binarySignature B)) (hsafe : AllBinariesSafe L.family) :
    ContainsInEquivalentStage L ∨ OddNormalized L.family := by
  rcases finite_group_split_height_one provedPaper1 L.family L.family_finite B hBmem hB hsafe
    with h | h
  · exact Or.inl (adjoin_weighted_equality L h)
  · exact Or.inr h

end
end Paper2.SourceFaithful.SourceStatements.WeightedEqualityStage

