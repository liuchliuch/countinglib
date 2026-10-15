import Paper2.SourceFaithful.LocalInputs
import Paper2.SourceFaithful.Synthesis.SameGraph
import Paper2.Synthesis.OneSided

/-! Original Section 9 common-side branch with canonical chosen-field answers.
Only the pure central-network semantics are reused from the old layer. -/
namespace Paper2.SourceFaithful.Synthesis
open Tractable ExactInput ExactInput.Computation Problem Paper2.Synthesis

/-- Actual encoded hardness follows from all-EO hardness with the very same
oracle program and graph bytes.  No ambient relative-EO assumption is used. -/
theorem one_sided_classification (PE : Paper1EOAccepted) (PR : Paper1RestrictionAccepted)
    (L : Language)
    (hpre : Preprocessed L.family) (heven : ∀ g ∈ L.family, Even g.1)
    (hside : CommonOneSided L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases heo : EOTract (centralFamily L.family)
  · exact Or.inl (tract_of_one_sided L hpre hside heo)
  · obtain ⟨H, hH⟩ := Language.coverage_family (centralFamily L.family)
      ((centralLanguage L).family_finite.subset (centralFamily_subset_centralLanguage L))
    have hsub : H.family ⊆ (centralLanguage L).family := by
      rw [hH]
      exact centralFamily_subset_centralLanguage L
    have hpH : Preprocessed H.family := by
      rw [hH]
      rintro g ⟨f, hf, hnz, rfl⟩
      exact ⟨(hpre f hf).1, hnz⟩
    have hardH := (PE.eo_2_16 H hpH (fun g hg => centralLanguage_allEO L heven g (hsub hg))).2
      (by simpa only [hH] using heo)
    have hard := hardH.transport (PR.restriction_2_5 H (centralLanguage L) hsub)
    right
    apply hard.sameGraph (centralInstanceEquiv L).symm
    · intro G
      exact (centralInstance_bytes L ((centralInstanceEquiv L).symm G)).symm.trans
        (congrArg _ ((centralInstanceEquiv L).apply_symm_apply G))
    · intro G
      exact (centralInstance_value L hside ((centralInstanceEquiv L).symm G)).symm.trans
        (congrArg _ ((centralInstanceEquiv L).apply_symm_apply G))


end Paper2.SourceFaithful.Synthesis

