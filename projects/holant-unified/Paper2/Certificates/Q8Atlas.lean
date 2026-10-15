import Paper2.Certificates.Q8AtlasClassification

/-! The atlas theorem for actual perfect-matching families. Matching indices
are introduced by the proved complete enumeration, not postulated as input. -/
namespace Paper2.Certificates.Q8.Atlas

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem deleted_pairs_complete (p q : Port) (h : p < q) :
    ∃ d : PairIndex, deleted d = (p,q) := by
  revert p q
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem deleted_pairs_injective : Function.Injective deleted := by
  decide +kernel

/-- The exact commuting-card predicate on actual mate functions. -/
def MatchingFamilyCompatible (M : (d : PairIndex) → Matching d) : Prop :=
  ∀ d e, DisjointDeleted d e →
    spliceMate (M d).extend e = spliceMate (M e).extend d

/-- Exact absence of a common edge for distinct overlapping deleted pairs. -/
def MatchingFamilyCollisionFree (M : (d : PairIndex) → Matching d) : Prop :=
  ∀ d e, d ≠ e → ¬DisjointDeleted d e →
    ¬∃ u v : Port, u ≠ v ∧ (M d).extend u = v ∧ (M e).extend u = v

/-- All actual normalized compatible families appear in the nine-leaf atlas. -/
theorem actual_normalized_atlas_cover (M : (d : PairIndex) → Matching d)
    (h : MatchingFamilyCompatible M) (h0 : (M 0).extend = fullMate 0 0) :
    ∃ r : Fin 9, ∀ d, (M d).extend = fullMate d (atlasRows r d) := by
  classical
  have hex : ∀ d, ∃ k : Choice, (M d).extend = fullMate d k :=
    fun d => (M d).exists_full_choice.exists
  choose f hf using hex
  have hcomp : DeckCompatible f := by
    intro d e hde
    change spliceMate (fullMate d (f d)) e = spliceMate (fullMate e (f e)) d
    rw [← hf d,← hf e]
    exact h d e hde
  have hn : f 0 = 0 := fullMate_injective 0 ((hf 0).symm.trans h0)
  obtain ⟨r,hr⟩ := normalized_atlas_cover f hcomp hn
  exact ⟨r,fun d => (hf d).trans (congrArg (fullMate d) (congrFun hr d))⟩

/-- The normalized form of A.8/A.9 for genuine residual perfect matchings.
The displayed relabeling is identity or 6↔7 after the initial normalization. -/
theorem actual_collision_free_translation (M : (d : PairIndex) → Matching d)
    (h : MatchingFamilyCompatible M) (h0 : (M 0).extend = fullMate 0 0)
    (hc : MatchingFamilyCollisionFree M) :
    ∃ p : Equiv.Perm Port, ∀ d v, v ≠ (deleted d).1 → v ≠ (deleted d).2 →
      p ((M d).extend v) = Fin.xor (p v) (Fin.xor (p (deleted d).1) (p (deleted d).2)) := by
  obtain ⟨r,hr⟩ := actual_normalized_atlas_cover M h h0
  have hcf : CollisionFree (atlasRows r) := by
    intro d e hne hde hedge
    apply hc d e hne hde
    obtain ⟨u,v,huv,hu,hv⟩ := hedge
    exact ⟨u,v,huv,(congrFun (hr d) u).trans hu,(congrFun (hr e) u).trans hv⟩
  obtain ⟨p,hp⟩ := normalized_collision_free_translation (atlasRows r)
    (atlas_rows_compatible r) (atlas_rows_normalized r) hcf
  refine ⟨p,?_⟩
  intro d v hleft hright
  rw [hr d]
  exact hp d v hleft hright

end Paper2.Certificates.Q8.Atlas
