import Paper2.HeightOne.Cyclic.ActualDeck
import Paper2.HeightOne.Cyclic.MatchingGeometry

/-! Equality-matching cards force common constraints on the original tensor.
The hypotheses in this algebraic leaf are supplied by `minimum_plusCard_matching`;
no tensor-primality or realizability is asserted for a coefficient slice. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open EndpointSelfLoop
variable {K : Type*} [Field K] {ι : Type} [Fintype ι]

lemma reindex_eq_zero_iff {κ : Type} (e : ι ≃ κ) (f : Tensor K ι) :
    Tensor.reindex e f = 0 ↔ f = 0 := by
  constructor
  · intro h
    funext x
    have he := congrFun h (fun j => x (e.symm j))
    simpa only [Tensor.reindex_apply, Equiv.symm_apply_apply, Pi.zero_apply] using he
  · rintro rfl
    rfl

lemma extendBits_origin_false (a b : ι) (hab : a ≠ b) :
    extendBits a b hab (fun _ => false) false false = (fun _ => false) := by
  classical
  funext i
  simp [extendBits, splitPorts]

def pairWord (a b : ι) : ι → Bool := by
  classical
  exact fun k => decide (k = a ∨ k = b)

lemma extendBits_origin_true (a b : ι) (hab : a ≠ b) :
    extendBits a b hab (fun _ => false) true true = pairWord a b := by
  classical
  funext i
  by_cases ha : i = a
  · subst i
    simp [extendBits, splitPorts, pairWord]
  · by_cases hb : i = b
    · subst i
      simp [extendBits, splitPorts, pairWord, Ne.symm hab]
    · simp [extendBits, splitPorts, pairWord, ha, hb, Sum.elim_inl]

/-- Every supported equal-bit lift projects into one and the same actual
matching code for this deleted pair. The pair need only have one visible card. -/
theorem common_matching_projection (f : Tensor K ι) (S : Set K)
    (hthree : ∃ s ∈ S, ∃ t ∈ S, ∃ u ∈ S, s ≠ t ∧ s ≠ u ∧ t ≠ u)
    (a b : ι) (hab : a ≠ b)
    (hcards : ∀ s ∈ S, plusContraction a b hab s f ≠ 0 →
      EqualityMatchingSupport (plusContraction a b hab s f))
    (hvisible : ∃ s ∈ S, plusContraction a b hab s f ≠ 0) :
    ∃ P : Pairing (Fintype.card (Remaining a b)),
      ∀ w, f w ≠ 0 → w a = w b →
        (fun j => w ((Fintype.equivFin (Remaining a b)).symm j).val) ∈ equalityCode P := by
  classical
  let e := Fintype.equivFin (Remaining a b)
  let A := Tensor.reindex e (fun x => f (extendBits a b hab x false false))
  let B := Tensor.reindex e (fun x => f (extendBits a b hab x true true))
  have hpencil (s : K) : pencil A B s = Tensor.reindex e (plusContraction a b hab s f) := by
    funext x
    simp only [A, B, pencil, Tensor.reindex_apply, plusContraction_apply]
  have hm : ∀ s ∈ S, pencil A B s ≠ 0 → ∃ P : Pairing (Fintype.card (Remaining a b)),
      support (pencil A B s) = equalityCode P := by
    intro s hs hn
    rw [hpencil] at hn ⊢
    exact hcards s hs (fun hz => hn ((reindex_eq_zero_iff e _).mpr hz))
  rcases phase_independent_matching A B S hthree hm with hzero | ⟨P, hP, _⟩
  · obtain ⟨s, hs, hn⟩ := hvisible
    apply False.elim
    apply hn
    apply (reindex_eq_zero_iff e _).mp
    rw [← hpencil]
    funext x
    simp [pencil, hzero.1, hzero.2]
  · refine ⟨P, ?_⟩
    intro w hw heq
    obtain ⟨s, hs, t, ht, u, hu, hst, _, _⟩ := hthree
    have hend := endpoint_pair_nonzero a b hab f w hw heq
    have hsurv := affine_survives_one_of_two hst hend
    have lift (q : K) (hq : q ∈ S)
        (hqv : f (extendBits a b hab (restrict a b w) false false) -
          q * f (extendBits a b hab (restrict a b w) true true) ≠ 0) :
        (fun j => w (e.symm j).val) ∈ equalityCode P := by
      have hval : pencil A B q (fun j => w (e.symm j).val) ≠ 0 := by
        rw [hpencil]
        change plusContraction a b hab q f (fun i => w (e.symm (e i)).val) ≠ 0
        have hew : (fun i : Remaining a b => w (e.symm (e i)).val) = EndpointSelfLoop.restrict a b w := by
          funext i
          simp [EndpointSelfLoop.restrict]
        rw [hew, plusContraction_apply]
        exact hqv
      rw [← hP q hq (fun hz => hval (congrFun hz _)), mem_support]
      exact hval
    exact hsurv.elim (lift s hs) (lift t ht)

/-- If all nonzero cards have matching support then every pair is visible as
soon as five ports are present. -/
theorem matching_cards_visible (f : Tensor K ι) (hf : f ≠ 0) (hn : 5 ≤ Fintype.card ι)
    (S : Set K) (s t : K) (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t)
    (hcards : ∀ a b (hab : a ≠ b), ∀ q ∈ S, plusContraction a b hab q f ≠ 0 →
      EqualityMatchingSupport (plusContraction a b hab q f)) :
    ∀ a b (hab : a ≠ b), plusContraction a b hab s f ≠ 0 ∨ plusContraction a b hab t f ≠ 0 := by
  apply every_pair_visible_of_origin_cards f hf hn s t hst
  intro a b hab
  exact ⟨fun h => (hcards a b hab s hs h).origin, fun h => (hcards a b hab t ht h).origin⟩

end
end Paper2.HeightOne.Cyclic
