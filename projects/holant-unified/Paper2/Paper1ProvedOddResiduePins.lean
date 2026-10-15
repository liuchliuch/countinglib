import Paper2.Paper1ProvedOddResidueNetwork
import Paper2.SourceFaithful.GadgetAugmentation

/-! The directed-pair residue has genuine oracle access to both unit pins
through actual scalar gadget installation and proved tensor-factor extraction.
The pins are members of an equivalent retained language, not asserted to be
actual graphs over the original nonprimitive odd family. -/
namespace Paper2.Paper1Proved.OddResidue
noncomputable section
open Paper2.Tractable Paper2.ExactInput Paper2.RelativeEO
set_option backward.isDefEq.respectTransparency false

/-- A real scalar directed-pair graph supplies both ordered pins with genuine
fixed-field reductions and all original labels retained. -/
theorem directed_pair_pins
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (Fac : SourceFaithful.Paper1FactorClosureAccepted)
    (L : Language) (hp : Preprocessed L.family) (hs : ¬ CommonOneSided L.family)
    (c : AlgebraicComplex) (hc : c ≠ 0)
    (hgraph : NetworkRealizable L.family (c • directedPair)) :
    ∃ M : Language,L.family ⊆ M.family ∧
      (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      Preprocessed M.family ∧ ¬ CommonOneSided M.family ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  obtain ⟨N,hN,hX,hval⟩ := hgraph.ordered
  obtain ⟨A,hA,hAL,hLA⟩ := G.adjoin_equivalence R L directedPair ⟨N,hN,hX,c,hc,hval⟩
  have hsub : L.family ⊆ A.family := by rw [hA]; exact Set.subset_insert _ _
  have hpair : (⟨2,directedPair⟩ : AnySignature AlgebraicComplex) ∈ A.family := by
    rw [hA]
    exact Set.mem_insert _ _
  have hpA : Preprocessed A.family := by
    rw [hA]
    rintro f (rfl | hf)
    · refine ⟨by decide,?_⟩
      intro hz
      have hh := congrFun hz ![false,true]
      simpa [directedPair] using hh
    · exact hp f hf
  have hsA : ¬ CommonOneSided A.family := by
    intro h
    exact hs (h.mono_family hsub)
  obtain ⟨M,hAM,h0,h1,hpM,hsM,hMA,hAMred⟩ :=
    SourceFaithful.RelativeEO.directedPair_factorClosure Fac A hpA hsA hpair
  exact ⟨M,hsub.trans hAM,h0,h1,hpM,hsM,hMA.trans hAL,hLA.trans hAMred⟩

end
end Paper2.Paper1Proved.OddResidue
