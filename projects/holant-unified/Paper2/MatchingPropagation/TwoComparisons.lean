import Paper2.MatchingPropagation.SingleFactor

namespace Paper2.MatchingPropagation
open CommonPhase EndpointSelfLoop
variable {ι : Type}

theorem avoids_iff_index (P : Matching ι) (j : Fin P.count) (e : PortPair ι) :
    Avoids P j e ↔ j ≠ (P.ports.symm e.first).1 ∧ j ≠ (P.ports.symm e.second).1 := by
  obtain ⟨a,b,hab⟩ := e
  obtain ⟨⟨k,s⟩,rfl⟩ := P.ports.surjective a
  obtain ⟨⟨l,t⟩,rfl⟩ := P.ports.surjective b
  cases s <;> cases t <;> simp [Avoids, and_comm]

theorem touches_index (P : Matching ι) (j : Fin P.count) (e : PortPair ι)
    (h : ¬Avoids P j e) :
    j = (P.ports.symm e.first).1 ∨ j = (P.ports.symm e.second).1 := by
  rw [avoids_iff_index] at h
  tauto

theorem endpoint_of_touches (P : Matching ι) (j : Fin P.count) (e : PortPair ι)
    (h : ¬Avoids P j e) : ∃ b : Bool, P.ports (j,b) = e.first ∨ P.ports (j,b) = e.second := by
  classical
  unfold Avoids at h
  push Not at h
  by_cases hf : P.ports (j,false) = e.first ∨ P.ports (j,false) = e.second
  · exact ⟨false,hf⟩
  · refine ⟨true,?_⟩
    tauto

theorem mate_of_same_index (P : Matching ι) (a b : ι) (hab : a ≠ b)
    (hi : (P.ports.symm a).1 = (P.ports.symm b).1) : mate P a = b := by
  rcases (index_eq_iff P b a).mp hi.symm with h | h
  · exact False.elim (hab h.symm)
  · exact h.symm

theorem pairs_of_two_distinct {α : Type*} {a b c d j k : α}
    (hjk : j ≠ k) (hj₁ : j = a ∨ j = b) (hk₁ : k = a ∨ k = b)
    (hj₂ : j = c ∨ j = d) (hk₂ : k = c ∨ k = d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases hj₁ with hj₁ | hj₁ <;> rcases hk₁ with hk₁ | hk₁ <;>
    rcases hj₂ with hj₂ | hj₂ <;> rcases hk₂ with hk₂ | hk₂ <;> aesop

/-- Two genuinely non-X factors, each hit by two disjoint deleted pairs, force
the first pair to become a spliced edge in the second contraction. -/
theorem two_touched_force (P : Matching ι) (p q : Fin P.count → ℂ)
    (c : ℂ) (hc : c ≠ 0) (hp : ∀ j, p j ≠ 0) (hq : ∀ j, q j ≠ 0)
    (r s : PortPair ι) (hrs : r.Disjoint s)
    (j k : Fin P.count) (hjk : j ≠ k)
    (hjr : ¬Avoids P j r) (hjs : ¬Avoids P j s)
    (hkr : ¬Avoids P k r) (hks : ¬Avoids P k s) :
    Forces (s.pairSum (product P p q c)) r.first r.second := by
  have h := pairs_of_two_distinct hjk (touches_index P j r hjr)
    (touches_index P k r hkr) (touches_index P j s hjs) (touches_index P k s hks)
  rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact pairSum_product_forces_splice P p q c hc hp hq s r.first r.second
      (mate_of_same_index P _ _ hrs.1 h₁)
      (mate_of_same_index P _ _ hrs.2.2.2 h₂)
      hrs.1 hrs.2.1 hrs.2.2.1 hrs.2.2.2
  · exact (pairSum_product_forces_splice P p q c hc hp hq s r.second r.first
      (mate_of_same_index P _ _ hrs.2.2.1 h₂)
      (mate_of_same_index P _ _ hrs.2.1 h₁)
      hrs.2.2.1 hrs.2.2.2 hrs.1 hrs.2.1).symm

/-- The central coefficient comparison in condition 2. The final obstruction
is a concrete support property of the actual second pair sum. -/
theorem weighted_isX_of_two_flat (P : Matching ι) (p q : Fin P.count → ℂ)
    (c : ℂ) (hc : c ≠ 0) (hp : ∀ j, p j ≠ 0) (hq : ∀ j, q j ≠ 0)
    (r s : PortPair ι) (hrs : r.Disjoint s)
    (hrn : ∃ x, r.pairSum (product P p q c) x ≠ 0)
    (hsn : ∃ x, s.pairSum (product P p q c) x ≠ 0)
    (hrf : Flat (r.pairSum (product P p q c)))
    (hsf : Flat (s.pairSum (product P p q c)))
    (hnot : ¬Forces (s.pairSum (product P p q c)) r.first r.second) :
    IsX (product P p q c) := by
  apply weighted_isX_of_equal P p q c hc hp
  intro j
  by_contra hj
  have hjr : ¬Avoids P j r := fun h => hj (surviving_factor_eq P p q c hp hq j r h hrn hrf)
  have hjs : ¬Avoids P j s := fun h => hj (surviving_factor_eq P p q c hp hq j s h hsn hsf)
  have hother : ∀ k, k ≠ j → p k = q k := by
    intro k hkj
    by_contra hk
    have hkr : ¬Avoids P k r := fun h => hk (surviving_factor_eq P p q c hp hq k r h hrn hrf)
    have hks : ¬Avoids P k s := fun h => hk (surviving_factor_eq P p q c hp hq k s h hsn hsf)
    exact hnot (two_touched_force P p q c hc hp hq r s hrs j k hkj.symm hjr hjs hkr hks)
  obtain ⟨b,hb⟩ := endpoint_of_touches P j s hjs
  have ha₁ : P.ports (j,b) ≠ r.first := by
    rcases hb with hb | hb
    · rw [hb]; exact hrs.1.symm
    · rw [hb]; exact hrs.2.1.symm
  have ha₂ : P.ports (j,b) ≠ r.second := by
    rcases hb with hb | hb
    · rw [hb]; exact hrs.2.2.1.symm
    · rw [hb]; exact hrs.2.2.2.symm
  exact hj (single_factor_eq P p q c hp hq j hother r b ha₁ ha₂ hrn hrf)

end Paper2.MatchingPropagation
