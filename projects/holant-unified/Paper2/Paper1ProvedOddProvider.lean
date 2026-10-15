import Paper2.SourceFaithful.Synthesis.OneSided
import Paper2.Paper1ProvedEOProvider
import Paper2.Paper1ProvedRestrictionProvider
import Paper2.Paper1ProvedCriteria
import Holant.Proofs.Hardness.GeneralOddResidueSource

/-! Actual original-input adapters for the ordinary odd source theorem.
The common-side arm is a same-graph EO reduction for arbitrary arity. The
primitive unary and nonprimitive residue consumers are supplied separately by
their proved physical source modules; no Paper 2 classification is used. -/
namespace Paper2.Paper1Proved.OddProvider
open Paper2.Tractable Paper2.ExactInput Paper2.ExactInput.Computation
open Paper2.Problem Paper2.Synthesis
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A nonzero central restriction itself proves even arity, even when the
original dictionary also contains odd rows. -/
theorem centralFamily_allEO (F : SignatureFamily AlgebraicComplex) :
    ∀ g ∈ centralFamily F, IsEO g := by
  rintro g ⟨f,_,hf,rfl⟩
  have hex : ∃ x, Signature.centralRestriction f.2 x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (funext h)
  obtain ⟨x,hx⟩ := hex
  have hc : 2 * weight x = f.1 := by
    by_contra h
    exact hx (by simp [Signature.centralRestriction,h])
  refine ⟨⟨weight x,?_⟩,?_⟩
  · change f.1 = 2 * weight x
    exact hc.symm
  · intro x hx
    exact by simp [Signature.centralRestriction,hx]

/-- The native common-side EO-failure reduction does not require even arity
of every original label: the actual nonzero central query labels are even. -/
theorem oneSided_failure_hard
    (E : Paper2.SourceFaithful.Paper1EOAccepted)
    (R : Paper2.SourceFaithful.Paper1RestrictionAccepted)
    (L : Language) (hp : Preprocessed L.family)
    (hs : CommonOneSided L.family) (hne : ¬ EOTract (centralFamily L.family)) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨H,hH⟩ := Language.coverage_family (centralFamily L.family)
    ((centralLanguage L).family_finite.subset (centralFamily_subset_centralLanguage L))
  have hsub : H.family ⊆ (centralLanguage L).family := by
    rw [hH]
    exact centralFamily_subset_centralLanguage L
  have hpH : Preprocessed H.family := by
    rw [hH]
    rintro g ⟨f,hf,hn,rfl⟩
    exact ⟨(hp f hf).1,hn⟩
  have he : ∀ g ∈ H.family, IsEO g := by
    rw [hH]
    exact centralFamily_allEO L.family
  have hardH := (E.eo_2_16 H hpH he).2 (by simpa only [hH] using hne)
  have hard := hardH.transport (R.restriction_2_5 H (centralLanguage L) hsub)
  apply hard.sameGraph (centralInstanceEquiv L).symm
  · intro G
    exact (centralInstance_bytes L ((centralInstanceEquiv L).symm G)).symm.trans
      (congrArg _ ((centralInstanceEquiv L).apply_symm_apply G))
  · intro G
    exact (centralInstance_value L hs ((centralInstanceEquiv L).symm G)).symm.trans
      (congrArg _ ((centralInstanceEquiv L).apply_symm_apply G))

/-- The actual one-sided arm returned by the frozen original odd source
reduces to the original ordinary problem through inverse K on the same graph. -/
theorem ordinary_oneSided_failure_hard (L : Language) (hp : Preprocessed L.family)
    (hs : CommonOneSided (kCoordinates L.family))
    (hne : ¬ EOTract (centralFamily (kCoordinates L.family))) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  apply Paper2.SourceFaithful.Synthesis.ordinary_hard_iff_inverseK_native L |>.mpr
  apply oneSided_failure_hard Paper2.Paper1Proved.eoProvider
    Paper2.Paper1Proved.restrictionProvider (inverseKLanguage L)
  · rw [inverseKLanguage_family]
    exact Conformal.preprocessed_familyAction _ hp
  · simpa only [inverseKLanguage_family] using hs
  · simpa only [inverseKLanguage_family] using hne

/-- Exact source-family form of the first original odd arm. -/
theorem source_oneSided_failure_hard (L : Language) (hp : Preprocessed L.family)
    (hs : Holant.Tractable.CommonOneSided
      (Holant.Tractable.kCoordinates (Holant.Tractable.preprocess
        (Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddUnarySource.original
          (signatures L)))))
    (hne : ¬ Holant.Tractable.EOTract (Holant.Tractable.centralFamily
      (Holant.Tractable.kCoordinates (Holant.Tractable.preprocess
        (Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddUnarySource.original
          (signatures L)))))) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  apply ordinary_oneSided_failure_hard L hp
  · change CommonOneSided (kCoordinates (preprocess L.family)) at hs
    simpa only [preprocess_eq_self hp] using hs
  · intro ht
    apply hne
    change Holant.Tractable.EOTract (centralFamily (kCoordinates (preprocess L.family)))
    rw [preprocess_eq_self hp]
    exact (eoTract_iff _).mp ht

/-- The primitive source arm consists of an actual nonzero original ordinary
unary and its proved controlled installation programme. -/
def PrimitiveCase (L : Language) : Prop :=
  GeneralOddResidueGcd.supportGcd (signatures L) = 1 ∧
    ∃ U : GeneralOddHighTerminalAccess.Actual (signatures L) 1,
      U.graph.denote ≠ 0 ∧
      Nonempty (GeneralOddHighTerminalAccess.Reduction (signatures L) U)

/-- The nonprimitive arm records its actual higher odd graph, exact source
lattice, endpoint-only diagnostic form, and the genuine absence of actual
original unaries. It contains no hardness conclusion. -/
def ResidueCase (L : Language) : Prop :=
  ∃ D : GeneralOddMinimalTerminal.Minimal (signatures L),
    3 ≤ D.arity ∧ D.arity = GeneralOddResidueGcd.supportGcd (signatures L) ∧
    Holant.Tractable.sourceKBasis.symm.action D.graph.denote =
      Holant.LocalDrafts.TetrahedralCompletion.ExternalOddCompletion.Structure.twoConstants
        (Holant.Tractable.sourceKBasis.symm.action D.graph.denote (fun _ => false))
        (Holant.Tractable.sourceKBasis.symm.action D.graph.denote (fun _ => true)) ∧
    Nonempty (GeneralOddHighTerminalAccess.Reduction (signatures L)
      (GeneralOddMinimalTerminal.actual (signatures L) D)) ∧
    ∀ U : GeneralOddHighTerminalAccess.Actual (signatures L) 1, U.graph.denote = 0

/-- The exact original odd source split, with its common-side EO-failure arm
already discharged by an actual canonical reduction. The other arms retain
their physical source data until their independent consumers are proved. -/
theorem hard_or_primitive_or_residue (L : Language) (hp : Preprocessed L.family)
    (hodd : ∃ g ∈ L.family, Odd g.1 ∧ g.2 ≠ 0) (hnot : ¬ Tract L.family) :
    FixedFieldOutput.SharpPHard .ordinary L ∨ PrimitiveCase L ∨ ResidueCase L := by
  obtain ⟨_,⟨j,rfl⟩,ho,hn⟩ := hodd
  have hnot' : ¬ Holant.Tractable.Tract (GeneralOddUnarySource.original (signatures L)) := by
    change ¬ Holant.Tractable.Tract L.family
    exact fun ht => hnot ((tract_iff _).mpr ht)
  rcases GeneralOddResidueSource.source_cases (signatures L) j ho hn hnot' with
    hs | hu | hd
  · exact Or.inl (source_oneSided_failure_hard L hp hs.1 hs.2)
  · exact Or.inr (Or.inl hu)
  · exact Or.inr (Or.inr hd)

/-- Specialization of the actual field-answer adapter to the original odd
source's ordinary Eq oracle. Both the original table labels and graph bytes
are copied literally; the answer conversion is the proved rational programme. -/
theorem ordinary_source_hard (L : Language)
    (hard : ∀ (A : Type) (ea : Computability.Encoding A Bool) (count : A → ℕ),
      Holant.Complexity.SharpPWitness ea count →
        Nonempty (Holant.Complexity.LengthControlledOracleReduction ea
          Computability.encodingNatBool (sourceEncoding L)
          (GeneralOddHighTerminalAccess.presentation (signatures L)).encoding
          count (GeneralOddHighTerminalAccess.targetValue (signatures L)))) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  let F := GeneralOddHighTerminalAccess.presentation (signatures L)
  let embed : GeneralOddHighTerminalAccess.field (signatures L) →ₗ[ℚ] AlgebraicComplex :=
    (GeneralOddHighTerminalAccess.field (signatures L)).val.toLinearMap
  apply canonicalFieldHard .ordinary L F embed Subtype.val_injective
    (GeneralOddHighTerminalAccess.targetValue (signatures L)) ?_ hard
  intro G
  change (GeneralOddHighTerminalAccess.targetValue (signatures L) G : AlgebraicComplex) = _
  rw [Holant.LocalDrafts.MainChain.OriginalFamily.value_exact]
  have h := network_value .ordinary L ((inputIso L).symm G)
  change (((inputIso L) ((inputIso L).symm G)).val.realize
    (((inputIso L) ((inputIso L).symm G)).property) (signatures L) (kernels .ordinary)).denote
      Fin.elim0 = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h

end
end Paper2.Paper1Proved.OddProvider
