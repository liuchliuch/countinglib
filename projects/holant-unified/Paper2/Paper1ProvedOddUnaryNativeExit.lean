import Paper2.Paper1ProvedOddUnaryResidual
import Paper2.Paper1ProvedOddUnaryAdjacent
import Paper2.Paper1ProvedNetwork
import Paper2.Synthesis.OrdinaryTransport

/-! An actual native unary graph is transported port for port to the ordinary
K-image language before the nonisotropic source selector is applied.  The
source remains an original-label Eq graph in that retained language, with
no inference of physical realizability from an arbitrary oracle reduction. -/
namespace Paper2.Paper1Proved.OddUnary.NativeExit
open Paper2.Tractable Paper2.ExactInput Paper2.ExactInput.Computation Paper2.Synthesis
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
noncomputable section
set_option backward.isDefEq.respectTransparency false

def ordinaryActual (L : Language) {n : ℕ} (M : Network AlgebraicComplex n)
    (hM : M.Uses L.family) (hX : M.NativeX) :
    GeneralOddHighTerminalAccess.Actual (signatures (kLanguage L)) n where
  graph := GeneralOddUnaryOrdinary.toOrdinary (sourceNetwork M)
  uses := by
    change Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction.Uses
      (GeneralOddUnaryOrdinary.toOrdinary (sourceNetwork M)) (kLanguage L).family
    rw [kLanguage_family]
    apply GeneralOddUnaryOrdinary.toOrdinary_uses (Paper2.kImage L) (sourceNetwork M)
    change Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction.Uses
      (sourceNetwork M) (Holant.Tractable.kCoordinates
        (Holant.Tractable.familyAction Holant.Tractable.sourceKBasis L.family))
    rw [Holant.Tractable.Conformal.kCoordinates_familyAction]
    exact hM
  ordinary := GeneralOddUnaryOrdinary.toOrdinary_ordinary _ hX

theorem ordinaryActual_denote (L : Language) {n : ℕ} (M : Network AlgebraicComplex n)
    (hM : M.Uses L.family) (hX : M.NativeX) :
    (ordinaryActual L M hM hX).graph.denote =
      Holant.Tractable.sourceKBasis.action M.denote :=
  GeneralOddUnaryOrdinary.toOrdinary_denote (sourceNetwork M)

theorem nonisotropic_hard_or_ternary
    (P : SourceFaithful.Paper1Accepted)
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (F : SourceFaithful.Paper1FactorClosureAccepted)
    (N : SourceFaithful.Paper1NormalizationAccepted)
    (L : Language) (hnot : ¬ Tract (Paper2.kImage L))
    (u : Signature AlgebraicComplex 1)
    (hgraph : NetworkRealizable L.family u)
    (hn : GeneralOddNonisotropicFrame.norm (Holant.Tractable.sourceKBasis.action u) ≠ 0) :
    FixedFieldOutput.SharpPHard .nativeX L ∨ Nonempty (TernarySource (kLanguage L)) := by
  obtain ⟨M,hM,hX,he⟩ := hgraph.ordered
  let U := ordinaryActual L M hM hX
  have hU : GeneralOddNonisotropicFrame.norm U.graph.denote ≠ 0 := by
    rw [ordinaryActual_denote,he]
    exact hn
  have hnotK : ¬ Tract (kLanguage L).family := by
    simpa only [kLanguage_family,Paper2.kImage] using hnot
  rcases Source.hard_or_ternary (kLanguage L) U hU hnotK P G R F N with hh | ht
  · exact Or.inl ((FixedFieldOutput.native_hard_iff L).mpr hh)
  · exact Or.inr ht

theorem adjacent_hard_or_ternary
    (P : SourceFaithful.Paper1Accepted)
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (F : SourceFaithful.Paper1FactorClosureAccepted)
    (N : SourceFaithful.Paper1NormalizationAccepted)
    (L : Language) (hnot : ¬ Tract (Paper2.kImage L))
    (h0 : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (h1 : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    {n : ℕ} (f : Signature AlgebraicComplex n)
    (hgraph : NetworkRealizable L.family f) (ha : Adjacent.adjacently_supported f) :
    FixedFieldOutput.SharpPHard .nativeX L ∨ Nonempty (TernarySource (kLanguage L)) := by
  obtain ⟨u,hu,_,_,hn⟩ := Adjacent.capped_unary_of_realizable L f hgraph h0 h1 ha
  exact nonisotropic_hard_or_ternary P G R F N L hnot u hu hn

theorem isotropic_unaries_of_nohard_no_ternary
    (P : SourceFaithful.Paper1Accepted)
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (F : SourceFaithful.Paper1FactorClosureAccepted)
    (N : SourceFaithful.Paper1NormalizationAccepted)
    (L : Language) (hnot : ¬ Tract (Paper2.kImage L))
    (hnohard : ¬ FixedFieldOutput.SharpPHard .nativeX L)
    (hnoternary : ¬ Nonempty (TernarySource (kLanguage L))) :
    ∀ u : Signature AlgebraicComplex 1, NetworkRealizable L.family u →
      GeneralOddNonisotropicFrame.norm (Holant.Tractable.sourceKBasis.action u) = 0 := by
  intro u hu
  by_contra hn
  rcases nonisotropic_hard_or_ternary P G R F N L hnot u hu hn with hh | ht
  · exact hnohard hh
  · exact hnoternary ht

theorem no_adjacent_of_nohard_no_ternary
    (P : SourceFaithful.Paper1Accepted)
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (F : SourceFaithful.Paper1FactorClosureAccepted)
    (N : SourceFaithful.Paper1NormalizationAccepted)
    (L : Language) (hnot : ¬ Tract (Paper2.kImage L))
    (hnohard : ¬ FixedFieldOutput.SharpPHard .nativeX L)
    (hnoternary : ¬ Nonempty (TernarySource (kLanguage L)))
    (h0 : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (h1 : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    {n : ℕ} (f : Signature AlgebraicComplex n)
    (hgraph : NetworkRealizable L.family f) : ¬ Adjacent.adjacently_supported f :=
  Adjacent.no_adjacent_realizable_of_isotropic_caps L h0 h1
    (isotropic_unaries_of_nohard_no_ternary P G R F N L hnot hnohard hnoternary) f hgraph

end
end Paper2.Paper1Proved.OddUnary.NativeExit

