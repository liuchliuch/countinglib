import Paper2.Paper1ProvedOddResidueAmplification
import Paper2.Paper1ProvedOddProvider
import Paper2.SourceFaithful.GeneralizedEqualityTerminal

/-! Ordinary high-odd endpoint consumers and retained pin resources. The
two-endpoint consumer uses the actual one-edge Gram graph already at arity
three. Its unary theorem dependency remains explicit, since deriving that
dependency from the ordinary odd theorem would be circular. -/
namespace Paper2.Paper1Proved.OddResidue
noncomputable section
open Paper2.Tractable Paper2.ExactInput Paper2.Synthesis
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
set_option backward.isDefEq.respectTransparency false

/-- A true original ordinary graph with two nonzero K endpoints is consumed
by the actual relative EO terminal, including the minimum odd arity three. -/
theorem ordinary_two_endpoint_hard
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (O : SourceFaithful.Paper1OccurrenceAccepted)
    (Fac : SourceFaithful.Paper1FactorClosureAccepted)
    (U : SourceFaithful.Paper1UnaryAccepted)
    (E : SourceFaithful.Paper1EOAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (B : SourceFaithful.Paper1BinaryInterpolationAccepted)
    (L : Language) (hp : Preprocessed L.family)
    (hs : ¬ CommonOneSided (kCoordinates L.family)) (hnot : ¬ Tract L.family)
    {q : ℕ} (hq : 3 ≤ q) (N : Holant.Network AlgebraicComplex q)
    (huses : Holant.Complexity.BinaryInterpolation.Chains.Uses N L.family)
    (hordinary : GeneralOddUnaryOrdinary.Ordinary N)
    (a b : AlgebraicComplex) (hab : a*b ≠ 0)
    (hform : Holant.Tractable.sourceKBasis.symm.action N.denote =
      Holant.LocalDrafts.TetrahedralCompletion.ExternalOddCompletion.Structure.twoConstants a b) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  apply SourceFaithful.Synthesis.ordinary_hard_iff_inverseK_native L |>.mpr
  have hpN : Preprocessed (inverseKLanguage L).family := by
    rw [inverseKLanguage_family]
    exact Conformal.preprocessed_familyAction _ hp
  have hboth : BothChargeSigns (inverseKLanguage L).family := by
    rw [inverseKLanguage_family]
    exact (commonOneSided_or_bothChargeSigns _).resolve_left hs
  have hnotN : ¬ Tract (Paper2.kImage (inverseKLanguage L)) := by
    simpa only [kImage_inverseKLanguage] using hnot
  have hgraph := fromSource_realizable _ (GeneralOddUnaryOrdinary.toNative N)
    (GeneralOddUnaryOrdinary.toNative_uses L.family N huses)
    (GeneralOddUnaryOrdinary.toNative_native N hordinary)
  rw [GeneralOddUnaryOrdinary.toNative_denote,hform] at hgraph
  have hgraphN : NetworkRealizable (inverseKLanguage L).family
      (Paper2.RelativeEO.generalizedEquality a b : Signature AlgebraicComplex q) := by
    rw [inverseKLanguage_family]
    exact hgraph
  apply SourceFaithful.generalized_equality_relative_terminal G O Fac U E R B
    (inverseKLanguage L) hpN hboth hnotN hq
    (Paper2.RelativeEO.generalizedEquality a b) a b hab
  · intro x
    rfl
  · exact hgraphN

/-- Both concrete high-residue resource arms produce retained unit pins,
with real reductions to the original inverse-K problem. -/
theorem higher_residue_pins
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (Fac : SourceFaithful.Paper1FactorClosureAccepted)
    (L : Language) (hp : Preprocessed L.family)
    (hodd : ∃ f ∈ L.family,Odd f.1 ∧ f.2 ≠ 0)
    (hs : ¬ CommonOneSided (kCoordinates L.family))
    (hd : 3 ≤ GeneralOddResidueGcd.supportGcd (signatures L)) :
    ∃ M : Language,(inverseKLanguage L).family ⊆ M.family ∧
      (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      Preprocessed M.family ∧ ¬ CommonOneSided M.family ∧
      FixedFieldOutput.Reduces .nativeX M (inverseKLanguage L) ∧
      FixedFieldOutput.Reduces .nativeX (inverseKLanguage L) M := by
  obtain ⟨_,⟨j,rfl⟩,hj,hn⟩ := hodd
  have hpN : Preprocessed (inverseKLanguage L).family := by
    rw [inverseKLanguage_family]
    exact Conformal.preprocessed_familyAction _ hp
  have hsN : ¬ CommonOneSided (inverseKLanguage L).family := by
    simpa only [inverseKLanguage_family] using hs
  rcases source_resources L j hj hn hs hd with h | h
  · obtain ⟨c,hc,hgraph⟩ := h
    apply directed_pair_pins G R Fac (inverseKLanguage L) hpN hsN c hc
    simpa only [inverseKLanguage_family] using hgraph
  · obtain ⟨c,hc,hgraph⟩ := h
    apply alternating_E_pins G R Fac (inverseKLanguage L) hpN hsN c hc
    simpa only [inverseKLanguage_family] using hgraph

/-- The genuinely proved high-residue pin extension isolates the remaining
ordinary-unary consumer. The unary theorem is an explicit input; this theorem
does not instantiate it using the ordinary odd theorem being assembled. -/
theorem higher_residue_hard
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (Fac : SourceFaithful.Paper1FactorClosureAccepted)
    (U : SourceFaithful.Paper1UnaryAccepted)
    (L : Language) (hp : Preprocessed L.family)
    (hodd : ∃ f ∈ L.family,Odd f.1 ∧ f.2 ≠ 0)
    (hs : ¬ CommonOneSided (kCoordinates L.family))
    (hnot : ¬ Tract L.family)
    (hd : 3 ≤ GeneralOddResidueGcd.supportGcd (signatures L)) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  obtain ⟨M,hLM,h0,_,_,_,hML,_⟩ := higher_residue_pins G R Fac L hp hodd hs hd
  apply SourceFaithful.Synthesis.ordinary_hard_iff_inverseK_native L |>.mpr
  rcases U.unary_3_4 M (TensorDecomposition.literalPin false)
    (TensorDecomposition.literalPin_ne_zero false) h0 with ht | hh
  · apply False.elim
    apply hnot
    rw [← kImage_inverseKLanguage L]
    exact ht.mono_family (familyAction_mono sourceKBasis hLM)
  · exact hh.transport hML

end
end Paper2.Paper1Proved.OddResidue

