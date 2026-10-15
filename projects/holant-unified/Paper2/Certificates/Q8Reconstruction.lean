import Paper2.Certificates.Q8DeckCompatibility
import Paper2.Certificates.Q8LabeledDeck

/-! The complete collision-free arity-eight route, from the actual source
contraction deck to a port-relabelled nonzero central Reed–Muller tensor. -/
namespace Paper2.Certificates.Q8.Atlas
open CommonPhase ReedMuller

/-- Lemmas A.9 and 8.10 with actual commuting contraction equations. The atlas
compatibility, initial matching normalization, and coefficient swap system are
all conclusions of proved bridges, not assumptions of this theorem. -/
theorem collision_free_deck_reedMuller (F : Signature ℂ 8) (lam : PortPair Port → ℂ)
    (P : (e : PortPair Port) → XMatching (EndpointSelfLoop.Remaining e.first e.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ e, lam e ≠ 0)
    (hc : MatchingFamilyCollisionFree (indexedMatching P))
    (heo : ∀ x, ReedMuller.weight x ≠ 4 → F x = 0) :
    ∃ (p : Equiv.Perm Port) (c : ℂ), c ≠ 0 ∧ labeledTensor p F = fun x => c * central x := by
  obtain ⟨p,hp⟩ := collision_free_translation (indexedMatching P)
    (matchingDeck_compatible F lam P hd hnz) hc
  obtain ⟨c,hc',he⟩ := scalar_central_of_labeled_deck F lam P hd hnz p hp heo
  exact ⟨p,c,hc',he⟩

/-- The same conclusion in the original named coordinates. -/
theorem collision_free_deck_reedMuller_original (F : Signature ℂ 8) (lam : PortPair Port → ℂ)
    (P : (e : PortPair Port) → XMatching (EndpointSelfLoop.Remaining e.first e.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ e, lam e ≠ 0)
    (hc : MatchingFamilyCollisionFree (indexedMatching P))
    (heo : ∀ x, ReedMuller.weight x ≠ 4 → F x = 0) :
    ∃ (p : Equiv.Perm Port) (c : ℂ), c ≠ 0 ∧
      ∀ x, F x = c * central (fun v => x (p.symm v)) := by
  obtain ⟨p,c,hc,he⟩ := collision_free_deck_reedMuller F lam P hd hnz hc heo
  refine ⟨p,c,hc,?_⟩
  intro x
  have h := congrFun he (fun v => x (p.symm v))
  simpa only [labeledTensor,p.symm_apply_apply] using h

end Paper2.Certificates.Q8.Atlas
