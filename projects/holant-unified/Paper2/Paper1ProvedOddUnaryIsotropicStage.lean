import Paper2.Paper1ProvedOddUnaryProvider
import Paper2.Paper1ProvedOddUnaryIsotropicPins
import Paper2.Paper1ProvedOddUnaryWeightedEquality
import Paper2.Paper1ProvedSingleWeightProvider
import Paper2.SourceFaithful.Synthesis.SameGraph

/-! The actual independent-isotropic pair is installed on its native chart.
The all-single-layer arm is consumed by the independent EO completion proof;
the remaining stage records only original-family inclusion, true reductions,
literal pins and the proved negative structural conditions. -/
namespace Paper2.Paper1Proved.OddUnary.IsotropicStage
open Paper2.Tractable Paper2.ExactInput Paper2.ExactInput.Computation Paper2.Synthesis
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure Retained (L : Language) : Type 1 where
  language : Language
  oldIncluded : (inverseKLanguage L).family ⊆ language.family
  pinZero : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ language.family
  pinOne : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ language.family
  preprocessed : Preprocessed language.family
  twoSided : ¬ CommonOneSided language.family
  backward : FixedFieldOutput.Reduces .nativeX language (inverseKLanguage L)
  forward : FixedFieldOutput.Reduces .nativeX (inverseKLanguage L) language
  nontractable : ¬ Tract (Paper2.kImage language)
  nonlayer : ¬ (∀ f ∈ language.family, ∃ d, Signature.SingleLayer f.2 d)

theorem Retained.transfer_hard {L : Language} (S : Retained L)
    (h : FixedFieldOutput.SharpPHard .nativeX S.language) :
    FixedFieldOutput.SharpPHard .ordinary L :=
  (SourceFaithful.Synthesis.ordinary_hard_iff_inverseK_native L).mpr (h.transport S.backward)

theorem hard_or_retained
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (F : SourceFaithful.Paper1FactorClosureAccepted)
    (E : SourceFaithful.Paper1EOAccepted)
    (L : Language) (hp : Preprocessed L.family) (hnot : ¬ Tract L.family)
    (pair : IsotropicPairSource L) :
    FixedFieldOutput.SharpPHard .ordinary L ∨ Nonempty (Retained L) := by
  classical
  obtain ⟨M,hsub,h0,h1,hpM,hsM,hML,hLM⟩ := IsotropicPins.isotropic_pair_pins
    G R L hp pair.first pair.second pair.firstIsotropic pair.secondIsotropic pair.pairingNonzero
  have hnotM : ¬ Tract (Paper2.kImage M) := by
    intro ht
    apply hnot
    have ho := ht.mono_family (familyAction_mono sourceKBasis hsub)
    change Tract (Paper2.kImage (inverseKLanguage L)) at ho
    simpa only [kImage_inverseKLanguage] using ho
  by_cases hlayer : ∀ f ∈ M.family, ∃ d, Signature.SingleLayer f.2 d
  · have hh := singleWeightHard G F E R M hpM hlayer
      (fun hex => hnotM (SourceFaithful.Synthesis.single_weight_exception_tract M hpM hlayer hex))
    exact Or.inl ((SourceFaithful.Synthesis.ordinary_hard_iff_inverseK_native L).mpr
      (hh.transport hML))
  · exact Or.inr ⟨⟨M,hsub,h0,h1,hpM,hsM,hML,hLM,hnotM,hlayer⟩⟩

theorem Retained.isotropic_unaries_of_nohard_no_ternary
    (P : SourceFaithful.Paper1Accepted)
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (F : SourceFaithful.Paper1FactorClosureAccepted)
    (N : SourceFaithful.Paper1NormalizationAccepted)
    {L : Language} (S : Retained L)
    (hnohard : ¬ FixedFieldOutput.SharpPHard .ordinary L)
    (hnoternary : ¬ Nonempty (TernarySource (kLanguage S.language))) :
    ∀ u : Signature AlgebraicComplex 1, NetworkRealizable S.language.family u →
      Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddNonisotropicFrame.norm
        (Holant.Tractable.sourceKBasis.action u) = 0 :=
  NativeExit.isotropic_unaries_of_nohard_no_ternary P G R F N S.language S.nontractable
    (fun h => hnohard (S.transfer_hard h)) hnoternary

theorem Retained.no_weightedEquality_of_nohard
    (P : SourceFaithful.Paper1Accepted)
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (N : SourceFaithful.Paper1NormalizationAccepted)
    {L : Language} (S : Retained L)
    (hnohard : ¬ FixedFieldOutput.SharpPHard .ordinary L)
    (f : Signature AlgebraicComplex 2)
    (hgraph : NativeNetworkRealizesUpTo S.language.family f) :
    ¬ Paper2.HeightTwo.WeightedEquality f :=
  WeightedEquality.no_weightedEquality_of_not_hard P G N S.language S.preprocessed
    S.nontractable (fun h => hnohard (S.transfer_hard h)) f hgraph

end
end Paper2.Paper1Proved.OddUnary.IsotropicStage

