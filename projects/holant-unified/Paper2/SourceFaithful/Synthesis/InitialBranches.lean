import Paper2.SourceFaithful.InitialBranches
import Paper2.SourceFaithful.Synthesis.OneSided
import Paper2.Synthesis.InitialBranches

/-! Additive canonical-field-output Section 9 initial branches. Root-coded input
languages and every preprocessing/exception premise are unchanged. -/
namespace Paper2.SourceFaithful.Synthesis
open Tractable ExactInput ExactInput.Computation Problem
open Paper2.Synthesis (tract_of_one_sided)

/-- A proved classification of the precise nonzero positive-arity sublanguage
returns to the original input, without deleting zero vertices in a graph. -/
theorem classification_from_preprocessed (PR : Paper1RestrictionAccepted) (L M : Language)
    (hM : M.family = preprocess L.family)
    (hclass : Tract (kImage M) ∨ FixedFieldOutput.SharpPHard .nativeX M) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  rcases hclass with ht | hh
  · exact Or.inl ((HeightTwo.kImage_preprocessed_tract_iff L M hM).mp ht)
  · right
    exact hh.transport (PR.restriction_2_5 M L (by rw [hM]; exact fun _ h => h.1))

/-- The source odd theorem is applied to the actual K-transformed finite table
family, then transferred back by the identical encoded oracle program. -/
theorem odd_classification_preprocessed (PO : Paper1OddAccepted) (L : Language)
    (hpre : Preprocessed L.family) (hodd : ∃ g ∈ L.family, Odd g.1 ∧ g.2 ≠ 0) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases ht : Tract (kImage L)
  · exact Or.inl ht
  · right
    apply (FixedFieldOutput.native_hard_iff L).mpr
    apply PO.odd_2_18 (kLanguage L)
    · rw [kLanguage_family]
      exact Conformal.preprocessed_familyAction _ hpre
    · obtain ⟨g, hg, ho, hn⟩ := hodd
      refine ⟨⟨g.1, sourceKBasis.action g.2⟩, ?_, ho, ?_⟩
      · rw [kLanguage_family]
        exact ⟨g, hg, rfl⟩
      · exact (Conformal.action_eq_zero_iff _ _).not.mpr hn
    · simpa only [kLanguage_family] using ht

/-- Arbitrary zero and nullary original labels are allowed. -/
theorem odd_classification (PO : Paper1OddAccepted) (PR : Paper1RestrictionAccepted)
    (L : Language) (hodd : ∃ g ∈ L.family, Odd g.1 ∧ g.2 ≠ 0) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨M, hM⟩ := Language.coverage_family (preprocess L.family)
    (L.family_finite.subset (fun _ h => h.1))
  apply classification_from_preprocessed PR L M hM
  apply odd_classification_preprocessed PO M
  · rw [hM]
    exact preprocess_preprocessed _
  · obtain ⟨g, hg, ho, hn⟩ := hodd
    refine ⟨g, ?_, ho, hn⟩
    rw [hM]
    exact ⟨hg, by obtain ⟨k, hk⟩ := ho; omega, hn⟩

theorem single_weight_exception_tract (L : Language) (hpre : Preprocessed L.family)
    (hlayers : ∀ g ∈ L.family, ∃ d, Signature.SingleLayer g.2 d)
    (hex : (CommonOneSided L.family ∧ EOTract (centralFamily L.family)) ∨
      (BothChargeSigns L.family ∧ EOTract (completionFamily L.family))) : Tract (kImage L) := by
  rcases hex with h | h
  · exact tract_of_one_sided L hpre h.1 h.2
  · have hp : Preprocessed (kImage L) := Conformal.preprocessed_familyAction _ hpre
    rw [Tract, preprocess_eq_self hp]
    refine ⟨L.family_finite.image _, Or.inr (Or.inl ?_)⟩
    simpa only [SingleWeightAlternative, kImage, Conformal.kCoordinates_familyAction] using
      And.intro hlayers h

theorem single_weight_classification_preprocessed (PS : Paper1SingleWeightAccepted)
    (L : Language) (hpre : Preprocessed L.family)
    (hlayers : ∀ g ∈ L.family, ∃ d, Signature.SingleLayer g.2 d) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases ht : Tract (kImage L)
  · exact Or.inl ht
  · exact Or.inr (PS.singleWeight_2_17 L hpre hlayers
      (fun h => ht (single_weight_exception_tract L hpre hlayers h)))

/-- This is the preliminary branching order from the source: common support
side is tested before any factor extraction, and single layers are separated. -/
theorem preliminary_branches (PO : Paper1OddAccepted) (PE : Paper1EOAccepted)
    (PS : Paper1SingleWeightAccepted) (PR : Paper1RestrictionAccepted)
    (L : Language) (hpre : Preprocessed L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L ∨
      ((∀ g ∈ L.family, Even g.1) ∧ ¬ CommonOneSided L.family ∧
        ¬ (∀ g ∈ L.family, ∃ d, Signature.SingleLayer g.2 d)) := by
  classical
  by_cases hodd : ∃ g ∈ L.family, Odd g.1 ∧ g.2 ≠ 0
  · rcases odd_classification_preprocessed PO L hpre hodd with ht | hh
    · exact Or.inl ht
    · exact Or.inr (Or.inl hh)
  have heven : ∀ g ∈ L.family, Even g.1 := by
    intro g hg
    rcases Nat.even_or_odd g.1 with he | ho
    · exact he
    · exact False.elim (hodd ⟨g, hg, ho, (hpre g hg).2⟩)
  by_cases hside : CommonOneSided L.family
  · rcases one_sided_classification PE PR L hpre heven hside with ht | hh
    · exact Or.inl ht
    · exact Or.inr (Or.inl hh)
  by_cases hlayers : ∀ g ∈ L.family, ∃ d, Signature.SingleLayer g.2 d
  · rcases single_weight_classification_preprocessed PS L hpre hlayers with ht | hh
    · exact Or.inl ht
    · exact Or.inr (Or.inl hh)
  exact Or.inr (Or.inr ⟨heven, hside, hlayers⟩)


end Paper2.SourceFaithful.Synthesis

