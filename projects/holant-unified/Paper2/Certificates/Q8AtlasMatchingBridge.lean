import Paper2.Certificates.Q8AtlasUnnormalized
import Paper2.MatchingPropagation.Basic

/-! The finite atlas accepts the actual oriented-port matching objects used
by the tensor propagation route; its input is not merely a table index. -/
namespace Paper2.Certificates.Q8.Atlas

/-- Forget only orientation and edge numbering, keeping every original mate. -/
def Matching.fromXMatching (d : PairIndex)
    (P : MatchingPropagation.Matching (Remaining d)) : Matching d where
  mate := MatchingPropagation.mate P
  involutive := MatchingPropagation.mate_mate P
  no_fixed := MatchingPropagation.mate_ne P

@[simp] theorem fromXMatching_mate (d : PairIndex)
    (P : MatchingPropagation.Matching (Remaining d)) (v : Remaining d) :
    (Matching.fromXMatching d P).mate v = MatchingPropagation.mate P v := rfl

/-- Atlas classification for actual matching-product port presentations. -/
theorem xMatching_collision_free_translation
    (P : (d : PairIndex) → MatchingPropagation.Matching (Remaining d))
    (h : MatchingFamilyCompatible (fun d => Matching.fromXMatching d (P d)))
    (h0 : (Matching.fromXMatching 0 (P 0)).extend = fullMate 0 0)
    (hc : MatchingFamilyCollisionFree (fun d => Matching.fromXMatching d (P d))) :
    ∃ p : Equiv.Perm Port, ∀ d v, v ≠ (deleted d).1 → v ≠ (deleted d).2 →
      p ((Matching.fromXMatching d (P d)).extend v) =
        Fin.xor (p v) (Fin.xor (p (deleted d).1) (p (deleted d).2)) :=
  actual_collision_free_translation _ h h0 hc

/-- Unnormalized A.9 for the actual matching-product port presentations. -/
theorem xMatching_translation
    (P : (d : PairIndex) → MatchingPropagation.Matching (Remaining d))
    (h : MatchingFamilyCompatible (fun d => Matching.fromXMatching d (P d)))
    (hc : MatchingFamilyCollisionFree (fun d => Matching.fromXMatching d (P d))) :
    ∃ p : Equiv.Perm Port, ∀ d v, v ≠ (deleted d).1 → v ≠ (deleted d).2 →
      p ((Matching.fromXMatching d (P d)).extend v) =
        Fin.xor (p v) (Fin.xor (p (deleted d).1) (p (deleted d).2)) :=
  collision_free_translation _ h hc

end Paper2.Certificates.Q8.Atlas
