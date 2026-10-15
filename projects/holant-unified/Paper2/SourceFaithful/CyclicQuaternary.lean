import Paper2.HeightOne.Cyclic.QuaternaryClosure
import Paper2.HeightOne.PhaseCards.Paper1Pencil
import Paper2.SourceFaithful.HeightTwo
import Paper2.SourceFaithful.GadgetAugmentation

/-! Source-faithful whole-language endpoint of the complete odd-cyclic
prime-quaternary proof, using actual native-X gadgets and fixed-field answers. -/
namespace Paper2.SourceFaithful.HeightOne
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Tractable ExactInput
open Paper2.HeightOne.PhaseCards Paper2.HeightOne.Cyclic
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup

/-- An actual tensor-prime four-port source in the complete safe odd-cyclic
group classifies the whole retained language. The paired RN deck, odd-root
normalization and exceptional two-copy obstruction are all proved internally. -/
theorem cyclic_prime_quaternary_classification
    (P : Paper1Accepted) (PG : Paper1DirectGadgetAccepted)
    (PR : Paper1RestrictionAccepted) (PF : Paper1FactorClosureAccepted)
    (PN : Paper1NormalizationAccepted) (L : Language) (hpre : Preprocessed L.family)
    {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (hG : actualClasses L.family = cyclicPhaseClasses N)
    (hsafe : AllBinariesSafe L.family)
    (f : Signature AlgebraicComplex 4) (hf : NetworkRealizable L.family f)
    (hp : TensorPrime f) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨C⟩ := rotationCards_nonempty (Or.inl hG)
  obtain ⟨g,hg,heven,hzero,hone⟩ :=
    actual_prime_quaternary_eightVertex provedPhasePencil hN hodd hG hsafe C f hf hp
  obtain ⟨M,hM,hML,_⟩ := PG.adjoin_equivalence PR L g
    (NativeNetworkRealizesUpTo.of_realizable hg)
  have hsub : L.family ⊆ M.family := by rw [hM]; exact Set.subset_insert _ _
  have hpreM : Preprocessed M.family := by
    intro k hk
    rw [hM] at hk
    rcases hk with rfl | hk
    · exact ⟨by change 0 < (4 : ℕ); decide, fun hz => hzero (congrFun hz _)⟩
    · exact hpre k hk
  have hmem : (⟨4,g⟩ : AnySignature AlgebraicComplex) ∈ M.family := by
    rw [hM]
    exact Set.mem_insert _ _
  rcases SourceFaithful.HeightTwo.eightVertex_classification_preprocessed P PF PN M hpreM
    g hmem heven hzero hone with ht | hh
  · exact Or.inl (ht.mono_family (familyAction_mono sourceKBasis hsub))
  · exact Or.inr (hh.transport hML)

end
end Paper2.SourceFaithful.HeightOne

