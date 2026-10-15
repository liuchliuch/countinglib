import Paper2.Paper1ProvedOddUnaryTernaryResidual
import Paper2.Paper1ProvedOddUnaryIsotropic
import Paper2.Paper1ProvedOddUnaryNativeExit
import Paper2.Paper1ProvedProvider
import Paper2.Paper1ProvedGadgetProvider
import Paper2.Paper1ProvedRestrictionProvider
import Paper2.Paper1ProvedFactorProvider
import Paper2.Paper1ProvedNormalizationProvider
import Paper2.SourceFaithful.Synthesis.InitialBranches

/-! Assembly of the original-unary source proof.  The two remaining consumers
are stated on their actual graph resources: an ordinary-isotropic W source,
or two independent ordinary-isotropic unaries.  The provider below makes
these precise mathematical inputs visible rather than treating a whole
unary classification as an upstream assumption. -/
namespace Paper2.Paper1Proved.OddUnary
open Paper2.Tractable Paper2.ExactInput Paper2.ExactInput.Computation
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Two actual ordinary Eq graphs over the unchanged input family.  Their
nonzero determinant and pairing are conclusions of physical extraction. -/
structure IsotropicPairSource (L : Language) : Type 1 where
  first : GeneralOddHighTerminalAccess.Actual (signatures L) 1
  second : GeneralOddHighTerminalAccess.Actual (signatures L) 1
  firstNonzero : first.graph.denote ≠ 0
  firstIsotropic : GeneralOddNonisotropicFrame.norm first.graph.denote = 0
  secondIsotropic : GeneralOddNonisotropicFrame.norm second.graph.denote = 0
  pairingNonzero : GeneralOddUnaryOrdinary.pairing first.graph.denote second.graph.denote ≠ 0
  determinantNonzero : GeneralOddUnaryOrdinary.determinant first.graph.denote second.graph.denote ≠ 0

namespace UnaryProvider

abbrev WConsumer := ∀ L : Language, IsotropicWSource L →
  FixedFieldOutput.SharpPHard .ordinary L

abbrev PairConsumer := ∀ L : Language, Preprocessed L.family → ¬ Tract L.family →
  IsotropicPairSource L → FixedFieldOutput.SharpPHard .ordinary L

/-- The ordinary source proof uses only the two explicit structural consumers;
all graph, normalization, restriction and factor providers are instantiated
with their proved implementations. -/
theorem ordinary_actual_hard (w : WConsumer) (pair : PairConsumer)
    (L : Language) (hp : Preprocessed L.family) (hnot : ¬ Tract L.family)
    (U : GeneralOddHighTerminalAccess.Actual (signatures L) 1)
    (hu : U.graph.denote ≠ 0) : FixedFieldOutput.SharpPHard .ordinary L := by
  by_cases hi : GeneralOddNonisotropicFrame.norm U.graph.denote = 0
  · rcases Isotropic.hard_or_ternary_or_isotropic_pair
        Paper2.Paper1Proved.provider Paper2.Paper1Proved.directGadgetProvider
        Paper2.Paper1Proved.restrictionProvider Paper2.Paper1Proved.factorProvider
        Paper2.Paper1Proved.normalizationProvider L hp U hu hi hnot with hard | source | independent
    · exact hard
    · obtain ⟨S⟩ := source
      rcases S.hard_or_isotropic_w Paper2.Paper1Proved.provider
          Paper2.Paper1Proved.directGadgetProvider Paper2.Paper1Proved.restrictionProvider
          Paper2.Paper1Proved.factorProvider Paper2.Paper1Proved.normalizationProvider with hard | source
      · exact hard
      · exact source.elim (w L)
    · obtain ⟨V,hv,hpair,hdet,_⟩ := independent
      exact pair L hp hnot ⟨U,V,hu,hi,hv,hpair,hdet⟩
  · rcases Source.hard_or_isotropic_w L U hi hnot Paper2.Paper1Proved.provider
        Paper2.Paper1Proved.directGadgetProvider Paper2.Paper1Proved.restrictionProvider
        Paper2.Paper1Proved.factorProvider Paper2.Paper1Proved.normalizationProvider with hard | source
    · exact hard
    · exact source.elim (w L)

/-- Every nonzero actual native unary, rather than only a literal unary row,
is transported through the proved ordinary K graph construction. -/
theorem native_actual_hard (w : WConsumer) (pair : PairConsumer)
    (L : Language) (hp : Preprocessed L.family) (hnot : ¬ Tract (Paper2.kImage L))
    (u : Signature AlgebraicComplex 1) (hu : u ≠ 0)
    (hgraph : NetworkRealizable L.family u) : FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨M,hM,hX,he⟩ := hgraph.ordered
  let U := NativeExit.ordinaryActual L M hM hX
  have hU : U.graph.denote ≠ 0 := by
    rw [NativeExit.ordinaryActual_denote,he]
    exact (Conformal.action_eq_zero_iff sourceKBasis u).not.mpr hu
  apply (FixedFieldOutput.native_hard_iff L).mpr
  apply ordinary_actual_hard w pair (kLanguage L) ?_ ?_ U hU
  · rw [kLanguage_family]
    exact Conformal.preprocessed_familyAction _ hp
  · simpa only [kLanguage_family] using hnot

theorem native_unary_preprocessed (w : WConsumer) (pair : PairConsumer)
    (L : Language) (hp : Preprocessed L.family)
    (u : Signature AlgebraicComplex 1) (hu : u ≠ 0)
    (hmem : (⟨1,u⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (Paper2.kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases ht : Tract (Paper2.kImage L)
  · exact Or.inl ht
  · right
    apply native_actual_hard w pair L hp ht u hu
    refine ⟨1,Network.corolla u,Equiv.refl _,?_,?_,?_⟩
    · intro v
      exact hmem
    · intro e
      exact Fin.elim0 e
    · simpa only [Tensor.reindex_refl] using Network.denote_corolla u

/-- Preprocessing and literal restriction return to the unchanged language,
including its original zero and nullary rows. -/
theorem native_unary (w : WConsumer) (pair : PairConsumer)
    (L : Language) (u : Signature AlgebraicComplex 1) (hu : u ≠ 0)
    (hmem : (⟨1,u⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (Paper2.kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨M,hM⟩ := Language.coverage_family (preprocess L.family)
    (L.family_finite.subset (fun _ h => h.1))
  apply SourceFaithful.Synthesis.classification_from_preprocessed
    Paper2.Paper1Proved.restrictionProvider L M hM
  apply native_unary_preprocessed w pair M
  · rw [hM]
    exact preprocess_preprocessed _
  · exact hu
  · rw [hM]
    exact ⟨hmem,by exact Nat.zero_lt_one,hu⟩

/-- A precise assembly factory, with its two genuine structural consumers
visible in the type.  This is not a closed unary classification theorem. -/
theorem providerOfResidualConsumers (w : WConsumer) (pair : PairConsumer) :
    SourceFaithful.Paper1UnaryAccepted where
  unary_3_4 := native_unary w pair

end UnaryProvider
end
end Paper2.Paper1Proved.OddUnary

