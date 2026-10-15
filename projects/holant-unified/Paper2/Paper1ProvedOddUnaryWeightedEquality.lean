import Paper2.SourceFaithful.HeightTwo
import Paper2.SourceFaithful.GadgetAugmentation

/-! A genuine nonsingular native diagonal binary is an unconditional local
exit.  Its actual graph is installed in the retained exact language, and the
proved global X-conformal normalization turns that binary into literal I.
The resulting hardness concerns the whole original oracle; no odd or unary
classification is used. -/
namespace Paper2.Paper1Proved.OddUnary.WeightedEquality
open Paper2.Tractable Paper2.ExactInput Paper2.HeightTwo
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem realized_hard
    (P : SourceFaithful.Paper1Accepted)
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (N : SourceFaithful.Paper1NormalizationAccepted)
    (L : Language) (hp : Preprocessed L.family)
    (hnot : ¬ Tract (kImage L))
    (f : Signature AlgebraicComplex 2) (hf : Paper2.HeightTwo.WeightedEquality f)
    (hgraph : NativeNetworkRealizesUpTo L.family f) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨M,hM,hML⟩ := G.adjoin L f hgraph
  have hsub : L.family ⊆ M.family := by
    rw [hM]
    exact Set.subset_insert _ _
  have hm : (⟨2,f⟩ : AnySignature AlgebraicComplex) ∈ M.family := by
    rw [hM]
    exact Set.mem_insert _ _
  have hpre : Preprocessed M.family := by
    rw [hM]
    rintro q (rfl | hq)
    · refine ⟨by change 0 < 2; decide,?_⟩
      intro hz
      exact hf.2.2.1 (congrFun hz _)
    · exact hp q hq
  rcases SourceFaithful.HeightTwo.weightedEquality_language_classification
      P N M hpre f hf hm with ht | hh
  · exact False.elim (hnot (ht.mono_family (familyAction_mono sourceKBasis hsub)))
  · exact hh.transport hML

theorem realizable_hard
    (P : SourceFaithful.Paper1Accepted)
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (N : SourceFaithful.Paper1NormalizationAccepted)
    (L : Language) (hp : Preprocessed L.family)
    (hnot : ¬ Tract (kImage L))
    (f : Signature AlgebraicComplex 2) (hf : Paper2.HeightTwo.WeightedEquality f)
    (hgraph : NetworkRealizable L.family f) :
    FixedFieldOutput.SharpPHard .nativeX L :=
  realized_hard P G N L hp hnot f hf (NativeNetworkRealizesUpTo.of_realizable hgraph)

theorem no_weightedEquality_of_not_hard
    (P : SourceFaithful.Paper1Accepted)
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (N : SourceFaithful.Paper1NormalizationAccepted)
    (L : Language) (hp : Preprocessed L.family)
    (hnot : ¬ Tract (kImage L))
    (hnohard : ¬ FixedFieldOutput.SharpPHard .nativeX L)
    (f : Signature AlgebraicComplex 2)
    (hgraph : NativeNetworkRealizesUpTo L.family f) :
    ¬ Paper2.HeightTwo.WeightedEquality f :=
  fun hf => hnohard (realized_hard P G N L hp hnot f hf hgraph)

end
end Paper2.Paper1Proved.OddUnary.WeightedEquality

