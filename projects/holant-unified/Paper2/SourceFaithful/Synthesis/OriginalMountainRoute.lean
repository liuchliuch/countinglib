import Paper2.SourceFaithful.Synthesis.GcdMountain

/-! The true Section 9 original-language mountain route, now using canonical
fixed-field oracle answers. The remaining mountain classification is explicit;
this is not a completed main dichotomy. -/
namespace Paper2.SourceFaithful.Synthesis
open Tractable ExactInput Problem

theorem preprocessed_hard_or_gcd_mountain
    (PO : Paper1OddAccepted) (PE : Paper1EOAccepted) (PS : Paper1SingleWeightAccepted)
    (PD : Paper1DirectGadgetAccepted) (PF : Paper1FactorClosureAccepted)
    (PR : Paper1RestrictionAccepted) (PU : Paper1UnaryAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hnot : ¬ Tract (kImage L)) :
    FixedFieldOutput.SharpPHard .nativeX L ∨ Nonempty (GcdMountainAugmentation L) := by
  rcases preliminary_branches PO PE PS PR L hpre with ht | hh | hcontinue
  · exact False.elim (hnot ht)
  · exact Or.inl hh
  · exact (gcd_mountain_or_hard PO PD PF PR PU L hpre hcontinue.2.1 hnot).symm

structure OriginalMountainRoute (original : Language) where
  seed : Language
  seedFamily : seed.family = preprocess original.family
  prepared : GcdMountainAugmentation seed
  forward : FixedFieldOutput.Reduces .nativeX prepared.language original
  criterionPullback : Tract (kImage prepared.language) → Tract (kImage original)

theorem OriginalMountainRoute.nontractable {L : Language} (A : OriginalMountainRoute L)
    (h : ¬ Tract (kImage L)) : ¬ Tract (kImage A.prepared.language) :=
  fun hM => h (A.criterionPullback hM)

theorem OriginalMountainRoute.transfer_hardness {L : Language} (A : OriginalMountainRoute L)
    (h : FixedFieldOutput.SharpPHard .nativeX A.prepared.language) : FixedFieldOutput.SharpPHard .nativeX L :=
  h.transport A.forward

/-- Every nontractable original table list either has already been proved hard,
or reaches a real positive-gcd mountain with all source Section 9 invariants. -/
theorem original_hard_or_gcd_mountain
    (PO : Paper1OddAccepted) (PE : Paper1EOAccepted) (PS : Paper1SingleWeightAccepted)
    (PD : Paper1DirectGadgetAccepted) (PF : Paper1FactorClosureAccepted)
    (PR : Paper1RestrictionAccepted) (PU : Paper1UnaryAccepted)
    (L : Language) (hnot : ¬ Tract (kImage L)) :
    FixedFieldOutput.SharpPHard .nativeX L ∨ Nonempty (OriginalMountainRoute L) := by
  obtain ⟨M, hM⟩ := Language.coverage_family (preprocess L.family)
    (L.family_finite.subset (fun _ h => h.1))
  have hpre : Preprocessed M.family := by rw [hM]; exact preprocess_preprocessed _
  have hnotM : ¬ Tract (kImage M) := fun h => hnot
    ((HeightTwo.kImage_preprocessed_tract_iff L M hM).mp h)
  have red : FixedFieldOutput.Reduces .nativeX M L :=
    PR.restriction_2_5 M L (by rw [hM]; exact fun _ h => h.1)
  rcases preprocessed_hard_or_gcd_mountain PO PE PS PD PF PR PU M hpre hnotM with hh | hA
  · exact Or.inl (hh.transport red)
  · obtain ⟨A⟩ := hA
    exact Or.inr ⟨{
      seed := M
      seedFamily := hM
      prepared := A
      forward := A.forward.trans red
      criterionPullback := fun h => (HeightTwo.kImage_preprocessed_tract_iff L M hM).mp
        (h.mono_family (familyAction_mono sourceKBasis A.original_subset)) }⟩


end Paper2.SourceFaithful.Synthesis

