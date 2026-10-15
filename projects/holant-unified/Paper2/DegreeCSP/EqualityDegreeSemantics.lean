import Paper2.DegreeCSP.EqualityDegreeTemplates
import Paper2.DegreeCSP.EqualityTemplateSemantics

namespace Paper2.DegreeCSP.EqualityDegreeTemplates
open Paper2.Tractable Paper2.ExactInput
noncomputable section

theorem make_denote (k : ℕ) (hk : 3 ≤ k) (d : ℕ) (hd : k ∣ d) :
    (make k hk d hd).denote = equality d := by
  by_cases h0 : d=0
  · subst d
    rw [make_zero,EqualityTemplates.nullary_denote k (by omega)]
  · rw [make_positive k hk d hd h0,Network.denote_reindexBoundary,
      EqualityTemplates.positive_denote _ _ hk (multiplicity_positive k hk d hd h0)]
    exact equality_reindex _ _ _

end
end Paper2.DegreeCSP.EqualityDegreeTemplates
