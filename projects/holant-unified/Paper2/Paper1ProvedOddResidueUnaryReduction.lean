import Paper2.Paper1ProvedOddResidueEquality
import Paper2.SourceFaithful.InitialBranches

/-! The complete ordinary odd source theorem reduces to a separately proved
ordinary-unary consumer. All physical graph and higher-residue producer arms
are discharged here; the unary record is deliberately an explicit argument.
In particular this module does not use unaryProviderOfOdd, which would make
the construction circular. -/
namespace Paper2.Paper1Proved.OddResidue
noncomputable section
open Paper2.Tractable Paper2.ExactInput Paper2.Synthesis
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
set_option backward.isDefEq.respectTransparency false

/-- Consume the genuine primitive original unary by its actual inverse-K
graph and a scalar-free controlled gadget installation. -/
theorem primitive_case_hard
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (U : SourceFaithful.Paper1UnaryAccepted)
    (L : Language) (hnot : ¬ Tract L.family) (hu : OddProvider.PrimitiveCase L) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  obtain ⟨_,N,hne,_⟩ := hu
  let f := Holant.Tractable.sourceKBasis.symm.action N.graph.denote
  have hf : f ≠ 0 := by
    intro hz
    apply hne
    have he := congrArg Holant.Tractable.sourceKBasis.action hz
    rw [Holant.Tractable.InvertibleKernel.action_symm_action] at he
    exact he.trans (Holant.Signature.coordinateAction_zero _)
  have hgraph := fromSource_realizable _ (GeneralOddUnaryOrdinary.toNative N.graph)
    (GeneralOddUnaryOrdinary.toNative_uses L.family N.graph N.uses)
    (GeneralOddUnaryOrdinary.toNative_native N.graph N.ordinary)
  rw [GeneralOddUnaryOrdinary.toNative_denote] at hgraph
  have hgraphN : NetworkRealizable (inverseKLanguage L).family f := by
    rw [inverseKLanguage_family]
    exact hgraph
  obtain ⟨M,hM,hML⟩ := G.adjoin_realizable (inverseKLanguage L) f hgraphN
  have hLM : (inverseKLanguage L).family ⊆ M.family := by
    rw [hM]
    exact Set.subset_insert _ _
  have hmem : (⟨1,f⟩ : AnySignature AlgebraicComplex) ∈ M.family := by
    rw [hM]
    exact Set.mem_insert _ _
  apply SourceFaithful.Synthesis.ordinary_hard_iff_inverseK_native L |>.mpr
  rcases U.unary_3_4 M f hf hmem with ht | hh
  · apply False.elim
    apply hnot
    rw [← kImage_inverseKLanguage L]
    exact ht.mono_family (familyAction_mono sourceKBasis hLM)
  · exact hh.transport hML

/-- Consume the exact residual source ledger, with the common-side arm
proved independently by EO and the other arm by actual retained pin access. -/
theorem residue_case_hard
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (Fac : SourceFaithful.Paper1FactorClosureAccepted)
    (U : SourceFaithful.Paper1UnaryAccepted)
    (L : Language) (hp : Preprocessed L.family)
    (hodd : ∃ f ∈ L.family,Odd f.1 ∧ f.2 ≠ 0)
    (hnot : ¬ Tract L.family) (hr : OddProvider.ResidueCase L) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  by_cases hs : CommonOneSided (kCoordinates L.family)
  · apply OddProvider.ordinary_oneSided_failure_hard L hp hs
    intro hEO
    apply hnot
    unfold Tract
    rw [preprocess_eq_self hp]
    exact ⟨L.family_finite,Or.inl ⟨hs,hEO⟩⟩
  · obtain ⟨D,hd,hg,_⟩ := hr
    apply higher_residue_hard G R Fac U L hp hodd hs hnot
    exact hg ▸ hd

/-- Actual ordinary odd assembly from an independent unary theorem. This
factory records exactly the remaining upstream theorem and has no implicit
ordinary odd assumption. -/
theorem oddProviderOfUnary
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (Fac : SourceFaithful.Paper1FactorClosureAccepted)
    (U : SourceFaithful.Paper1UnaryAccepted) : SourceFaithful.Paper1OddAccepted := by
  refine ⟨?_⟩
  intro L hp hodd hnot
  exact by
    rcases OddProvider.hard_or_primitive_or_residue L hp hodd hnot with hh | hu | hr
    · exact hh
    · exact primitive_case_hard G U L hnot hu
    · exact residue_case_hard G R Fac U L hp hodd hnot hr

end
end Paper2.Paper1Proved.OddResidue

