import Paper2.HeightOne.Cyclic.MatchingDeck

/-! The original Walsh tensor has a nonzero constant coefficient above arity
four. This follows from the proved common matching, not an assumed normal form. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open EndpointSelfLoop
variable {K : Type*} [Field K]

lemma pairWord_projected {n : ℕ} (a b : Fin n) (u v : Remaining a b) :
    (fun j => pairWord u.val v.val ((Fintype.equivFin (Remaining a b)).symm j).val) =
      weightTwoWord ((Fintype.equivFin (Remaining a b)) u)
        ((Fintype.equivFin (Remaining a b)) v) := by
  classical
  funext j
  simp only [pairWord, weightTwoWord]
  congr 1
  have hx (w : Remaining a b) :
      ((Fintype.equivFin (Remaining a b)).symm j).val = w.val ↔
        j = (Fintype.equivFin (Remaining a b)) w := by
    rw [← Subtype.ext_iff]
    exact (Fintype.equivFin (Remaining a b)).symm_apply_eq
  exact propext (or_congr (hx u) (hx v))

/-- Source cyclic-collapse Step 1, in a field-independent form. Five ports
already suffice for this support-only conclusion. -/
theorem origin_nonzero_of_matching_cards {n : ℕ} (f : Signature K n) (hf : f ≠ 0)
    (hn : 5 ≤ n) (S : Set K)
    (hthree : ∃ s ∈ S, ∃ t ∈ S, ∃ u ∈ S, s ≠ t ∧ s ≠ u ∧ t ≠ u)
    (hcards : ∀ a b (hab : a ≠ b), ∀ q ∈ S, plusContraction a b hab q f ≠ 0 →
      EqualityMatchingSupport (plusContraction a b hab q f)) : f (fun _ => false) ≠ 0 := by
  classical
  intro hf0
  obtain ⟨s, hs, t, ht, u, hu, hst, hsu, htu⟩ := hthree
  have hvis := matching_cards_visible f hf (by simpa using hn) S s t hs ht hst hcards
  have hpairs (a b : Fin n) (hab : a ≠ b) : f (pairWord a b) ≠ 0 := by
    have aux (q : K) (hq : q ∈ S) (hqn : plusContraction a b hab q f ≠ 0) : f (pairWord a b) ≠ 0 := by
      have h0 := (hcards a b hab q hq hqn).origin
      rw [plusContraction_apply, extendBits_origin_false, extendBits_origin_true, hf0] at h0
      intro hz
      exact h0 (by simp [hz])
    exact (hvis a b hab).elim (aux s hs) (aux t ht)
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a, b] at this
  have hvisible : ∃ q ∈ S, plusContraction a b hab q f ≠ 0 :=
    (hvis a b hab).elim (fun h => ⟨s, hs, h⟩) (fun h => ⟨t, ht, h⟩)
  obtain ⟨P, hP⟩ := common_matching_projection f S
    ⟨s, hs, t, ht, u, hu, hst, hsu, htu⟩ a b hab (hcards a b hab) hvisible
  apply not_all_weightTwo_supported P (by have h := remaining_card a b hab; simp only [Fintype.card_fin] at h; omega)
  intro p q hpq
  let e := Fintype.equivFin (Remaining a b)
  let p' := e.symm p
  let q' := e.symm q
  have hpq' : p'.val ≠ q'.val := by
    intro h
    exact hpq (e.symm.injective (Subtype.ext h))
  have heq : pairWord p'.val q'.val a = pairWord p'.val q'.val b := by
    simp [pairWord, Ne.symm p'.property.1, Ne.symm q'.property.1,
      Ne.symm p'.property.2, Ne.symm q'.property.2]
  have h := hP (pairWord p'.val q'.val) (hpairs _ _ hpq') heq
  rw [pairWord_projected] at h
  simpa only [p', q', e, Equiv.apply_symm_apply] using h

end
end Paper2.HeightOne.Cyclic
