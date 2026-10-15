import Paper2.SourceFaithful.HeightFour.Diagonal
import Paper2.SourceFaithful.BellTerminal
import Paper2.SourceFaithful.RelativeEO.TwoLevelSixTerminal
import Paper2.ReedMullerNormalization.Network

/-! Complete native-X complexity classification for the canonical complete
height-four RM mountain. Endpoint imbalance is an actual five-edge gadget;
the balanced case uses one global conformal basis and the proved Bell machine. -/
namespace Paper2.SourceFaithful.HeightFour
open Tractable ExactInput ReedMullerNormalization BellReduction

theorem canonical_source_highCharge (A B c : AlgebraicComplex) :
    Even (8 : ℕ) ∧ Tensor.HalfChargeDivisible (source A B c) 4 := by
  refine ⟨by decide,?_⟩
  intro x hx
  by_cases h0 : x = zeroWord
  · subst x
    change (4 : ℤ) ∣ halfCharge (fun _ : Fin (2 * 4) => false)
    rw [halfCharge_false]
    norm_num
  by_cases h1 : x = oneWord
  · subst x
    change (4 : ℤ) ∣ halfCharge (fun _ : Fin (2 * 4) => true)
    rw [halfCharge_true]
    norm_num
  have hcen : ReedMuller.IsCentral x := by
    by_contra hn
    exact hx (by simp [source,ReedMuller.central,h0,h1,hn])
  have hw : Paper2.weight x = ReedMuller.weight x := by
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> rfl
  simp only [halfCharge,Fintype.card_fin,hw,hcen.2]
  norm_num

theorem canonical_source_ne_zero (A B c : AlgebraicComplex) (hA : A ≠ 0) :
    source A B c ≠ 0 := by
  intro hz
  exact hA (by simpa [source,ReedMuller.central] using congrFun hz (zeroWord : ReedMuller.Word))

/-- The canonical mountain need only be realized by an actual original graph.
It is retained through a proved direct-gadget reduction before classification. -/
theorem canonical_realized_hard
    (P : Paper1Accepted) (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (N : Paper1NormalizationAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hHigh : HighCharge L.family) (hnot : ¬ Tract (kImage L))
    (A B c : AlgebraicComplex) (hab : A * B ≠ 0) (hc : c ≠ 0)
    (hgraph : NetworkRealizable L.family (source A B c)) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  have hA : A ≠ 0 := (mul_ne_zero_iff.mp hab).1
  obtain ⟨S,hS,hLS,hpreS,hbothS,hnotS,hSL⟩ :=
    RelativeEO.retained_output G L hpre hboth hnot (source A B c) (by decide)
      (canonical_source_ne_zero A B c hA) (NativeNetworkRealizesUpTo.of_realizable hgraph)
  have hmem : (⟨8,source A B c⟩ : AnySignature AlgebraicComplex) ∈ S.family := by
    rw [hS]
    exact Set.mem_insert _ _
  have hHighS : HighCharge S.family := by
    rw [hS]
    intro f hf
    rcases hf with rfl | hf
    · exact canonical_source_highCharge A B c
    · exact hHigh f hf
  by_cases hAB : A * B = c ^ 2
  · obtain ⟨T,hHighT,hnotT,hcore,hTS,_⟩ :=
      canonical_normalization N S hpreS hHighS hnotS A B c hA hc hAB hmem
    exact (BellTerminal.rm8_hard P T hHighT hnotT c hc hcore).transport
      (hTS.trans hSL)
  · exact (RelativeEO.sixOutput_hard G O F U E R S hpreS hbothS hnotS A B c hc hAB
      (sixOutput_realizable A B c S.family hmem)).transport hSL

end Paper2.SourceFaithful.HeightFour
