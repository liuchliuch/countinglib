import Paper2.Certificates.Q8Reconstruction
import Paper2.HighHeightReconstruction.Source

/-! The complete arity-eight atlas dichotomy, with the coefficient recovered
from an actual algebraic input entry. No atlas or coefficient classification
is a caller premise: compatibility comes from commuting native contractions. -/
namespace Paper2.Certificates.Q8.Atlas
open CommonPhase EndpointSelfLoop MatchingPropagation HighHeightReconstruction ReedMuller

theorem same_pair_index (d e : PairIndex) :
    SamePair (portPair d) (portPair e) ↔ d = e := by
  unfold SamePair portPair
  revert d e
  decide +kernel

theorem Matching.edge_remaining {d : PairIndex} (M : Matching d)
    (u v : Port) (huv : u ≠ v) (h : M.extend u = v) :
    (u ≠ (deleted d).1 ∧ u ≠ (deleted d).2) ∧
      (v ≠ (deleted d).1 ∧ v ≠ (deleted d).2) := by
  have hu : u ≠ (deleted d).1 ∧ u ≠ (deleted d).2 := by
    by_contra hn
    have hh := M.extend_off u (outside_or_deleted u _ _ hn)
    exact huv (hh.symm.trans h)
  exact ⟨hu, h ▸ M.extend_remaining u hu⟩

/-- Failure of the literal atlas collision-free condition supplies the exact
shared-edge hypotheses of the proved eight-port reconstruction theorem. -/
theorem matching_deck_of_collision (F : Signature ℂ 8)
    (hF : Tensor.ChargeLayer F 0) (lam : PortPair Port → ℂ)
    (P : (r : PortPair Port) → XMatching (EndpointSelfLoop.Remaining r.first r.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ r, lam r ≠ 0)
    (hc : ¬ MatchingFamilyCollisionFree (indexedMatching P)) : IsX F := by
  classical
  unfold MatchingFamilyCollisionFree at hc
  push Not at hc
  obtain ⟨d,e,hde,hmeet,u,v,huv,hdu,hev⟩ := hc
  have hud := (indexedMatching P d).edge_remaining u v huv hdu
  have hue := (indexedMatching P e).edge_remaining u v huv hev
  let r := portPair d
  let s := portPair e
  let t : PortPair Port := ⟨u,v,huv⟩
  have hrt : r.Disjoint t :=
    ⟨hud.1.1.symm,hud.2.1.symm,hud.1.2.symm,hud.2.2.symm⟩
  have hst : s.Disjoint t :=
    ⟨hue.1.1.symm,hue.2.1.symm,hue.1.2.symm,hue.2.2.symm⟩
  have hdr : EdgeIn P r t hrt := by
    apply Subtype.ext
    change (MatchingPropagation.mate (P (portPair d))
      (⟨u,hud.1⟩ : EndpointSelfLoop.Remaining (portPair d).first (portPair d).second)).val = v
    rw [← indexedMatching_extend P d u hud.1]
    exact hdu
  have her : EdgeIn P s t hst := by
    apply Subtype.ext
    change (MatchingPropagation.mate (P (portPair e))
      (⟨u,hue.1⟩ : EndpointSelfLoop.Remaining (portPair e).first (portPair e).second)).val = v
    rw [← indexedMatching_extend P e u hue.1]
    exact hev
  exact (reconstruct_of_shared_overlap (by simp) F hF lam P hd hnz r s t
    (fun h => hde ((same_pair_index d e).mp h)) hmeet hrt hst hdr her).1

private theorem reference_plane : IsCentral (fromMask 85) := by decide +kernel

/-- The central coefficient is an actual algebraic input-table entry at a
labelled affine plane, rather than an arbitrary complex scalar. -/
theorem collision_free_deck_reedMuller_algebraic
    (F : Signature Tractable.AlgebraicComplex 8) (lam : PortPair Port → ℂ)
    (P : (r : PortPair Port) → XMatching (EndpointSelfLoop.Remaining r.first r.second))
    (hd : MatchingDeck (fun x => (F x : ℂ)) lam P) (hnz : ∀ r, lam r ≠ 0)
    (hc : MatchingFamilyCollisionFree (indexedMatching P))
    (heo : ∀ x, ReedMuller.weight x ≠ 4 → F x = 0) :
    ∃ (p : Equiv.Perm Port) (c : Tractable.AlgebraicComplex), c ≠ 0 ∧
      labeledTensor p F = fun x => c * central x := by
  obtain ⟨p,z,hz,he⟩ := collision_free_deck_reedMuller
    (fun x => (F x : ℂ)) lam P hd hnz hc (fun x hx => by rw [heo x hx]; rfl)
  let c : Tractable.AlgebraicComplex := labeledTensor p F (fromMask 85)
  have hcz : (c : ℂ) = z := by
    have hh := congrFun he (fromMask 85)
    simpa only [c,labeledTensor,central,reference_plane,ite_true,mul_one] using hh
  refine ⟨p,c,?_,?_⟩
  · intro hc0
    apply hz
    rw [← hcz,hc0]
    rfl
  · funext x
    apply Subtype.ext
    have hh := congrFun he x
    by_cases hx : IsCentral x <;>
      simpa [labeledTensor,central,hx,hcz] using hh

end Paper2.Certificates.Q8.Atlas
