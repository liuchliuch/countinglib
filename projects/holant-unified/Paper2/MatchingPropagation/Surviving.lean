import Paper2.MatchingPropagation.Basic

namespace Paper2.MatchingPropagation
open CommonPhase EndpointSelfLoop
variable {ι : Type} {K : Type*}

noncomputable def edgeSet (P : Matching ι) (j : Fin P.count)
    (x : ι → Bool) (t : Bool) : ι → Bool := by
  classical
  exact fun a => if (P.ports.symm a).1 = j then
    if (P.ports.symm a).2 then !t else t else x a

@[simp] theorem edgeSet_port (P : Matching ι) (j : Fin P.count)
    (x : ι → Bool) (t b : Bool) :
    edgeSet P j x t (P.ports (j,b)) = if b then !t else t := by
  classical
  simp [edgeSet]

theorem edgeSet_other (P : Matching ι) (j k : Fin P.count) (h : k ≠ j)
    (x : ι → Bool) (t b : Bool) :
    edgeSet P j x t (P.ports (k,b)) = x (P.ports (k,b)) := by
  classical
  simp [edgeSet,h]

noncomputable def rest [CommRing K] (P : Matching ι) (p q : Fin P.count → K)
    (c : K) (j : Fin P.count) : Tensor K ι := by
  classical
  exact fun x => c * ∏ k ∈ Finset.univ.erase j,
    WeightedMatching.binary (p k) (q k) (x (P.ports (k,false))) (x (P.ports (k,true)))

theorem product_factor [CommRing K] (P : Matching ι) (p q : Fin P.count → K)
    (c : K) (j : Fin P.count) (x : ι → Bool) :
    product P p q c x =
      WeightedMatching.binary (p j) (q j) (x (P.ports (j,false))) (x (P.ports (j,true))) *
        rest P p q c j x := by
  classical
  rw [product, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp [rest,mul_assoc,mul_comm,mul_left_comm]

theorem rest_edgeSet [CommRing K] (P : Matching ι) (p q : Fin P.count → K)
    (c : K) (j : Fin P.count) (x : ι → Bool) (t : Bool) :
    rest P p q c j (edgeSet P j x t) = rest P p q c j x := by
  classical
  unfold rest
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  have hkj := (Finset.mem_erase.mp hk).1
  rw [edgeSet_other P j k hkj, edgeSet_other P j k hkj]

/-- An edge is untouched by deletion exactly when both original occurrences survive. -/
def Avoids (P : Matching ι) (j : Fin P.count) (e : PortPair ι) : Prop :=
  P.ports (j,false) ≠ e.first ∧ P.ports (j,false) ≠ e.second ∧
  P.ports (j,true) ≠ e.first ∧ P.ports (j,true) ≠ e.second

theorem edgeSet_fill (P : Matching ι) (j : Fin P.count) (e : PortPair ι)
    (h : Avoids P j e) (x : ι → Bool) (s t : Bool) :
    edgeSet P j (e.fill x s) t = e.fill (edgeSet P j x t) s := by
  classical
  obtain ⟨ha,hb,hc,hd⟩ := h
  funext a
  obtain ⟨⟨k,b⟩,rfl⟩ := P.ports.surjective a
  by_cases hkj : k = j
  · subst k
    cases b <;> simp [edgeSet,PortPair.fill,ha,hb,hc,hd]
  · have h₁ : (P.ports.symm e.first).1 ≠ j := by
      intro hj
      have he : P.ports (j,(P.ports.symm e.first).2) = e.first := by
        simpa [← hj] using P.ports.apply_symm_apply e.first
      cases hh : (P.ports.symm e.first).2 <;> simp_all
    have h₂ : (P.ports.symm e.second).1 ≠ j := by
      intro hj
      have he : P.ports (j,(P.ports.symm e.second).2) = e.second := by
        simpa [← hj] using P.ports.apply_symm_apply e.second
      cases hh : (P.ports.symm e.second).2 <;> simp_all
    simp only [edgeSet, Equiv.symm_apply_apply, if_neg hkj]
    by_cases hfirst : P.ports (k,b) = e.first
    · simp [PortPair.fill,hfirst,h₁]
    · by_cases hsecond : P.ports (k,b) = e.second
      · simp [PortPair.fill,hsecond,h₂,e.distinct.symm]
      · simp [PortPair.fill,hfirst,hsecond,edgeSet,hkj]

theorem pairSum_factor [CommRing K] (P : Matching ι) (p q : Fin P.count → K)
    (c : K) (j : Fin P.count) (e : PortPair ι) (h : Avoids P j e)
    (x : ι → Bool) :
    e.pairSum (product P p q c) x =
      WeightedMatching.binary (p j) (q j) (x (P.ports (j,false))) (x (P.ports (j,true))) *
        e.pairSum (rest P p q c j) x := by
  unfold PortPair.pairSum
  simp only [product_factor P p q c j, fill_other e x _ _ h.1 h.2.1,
    fill_other e x _ _ h.2.2.1 h.2.2.2, Finset.mul_sum]

theorem pairSum_rest_edgeSet [CommRing K] (P : Matching ι) (p q : Fin P.count → K)
    (c : K) (j : Fin P.count) (e : PortPair ι) (h : Avoids P j e)
    (x : ι → Bool) (t : Bool) :
    e.pairSum (rest P p q c j) (edgeSet P j x t) =
      e.pairSum (rest P p q c j) x := by
  unfold PortPair.pairSum
  simp only [← edgeSet_fill P j e h, rest_edgeSet]

/-- Rigidity of a genuinely surviving binary factor. Equality is obtained from
actual two-state sums and two nonzero coefficients, with no UPF assumption. -/
theorem surviving_factor_eq (P : Matching ι) (p q : Fin P.count → ℂ)
    (c : ℂ) (hp : ∀ j, p j ≠ 0) (hq : ∀ j, q j ≠ 0)
    (j : Fin P.count) (e : PortPair ι) (h : Avoids P j e)
    (hnz : ∃ x, e.pairSum (product P p q c) x ≠ 0)
    (hflat : Flat (e.pairSum (product P p q c))) : p j = q j := by
  obtain ⟨x,hx⟩ := hnz
  have hrest : e.pairSum (rest P p q c j) x ≠ 0 := by
    intro hz
    apply hx
    rw [pairSum_factor P p q c j e h, hz, mul_zero]
  have hf : e.pairSum (product P p q c) (edgeSet P j x false) =
      p j * e.pairSum (rest P p q c j) x := by
    rw [pairSum_factor P p q c j e h, pairSum_rest_edgeSet P p q c j e h]
    simp [WeightedMatching.binary]
  have ht : e.pairSum (product P p q c) (edgeSet P j x true) =
      q j * e.pairSum (rest P p q c j) x := by
    rw [pairSum_factor P p q c j e h, pairSum_rest_edgeSet P p q c j e h]
    simp [WeightedMatching.binary]
  have he := hflat (edgeSet P j x false) (edgeSet P j x true)
    (by rw [hf]; exact mul_ne_zero (hp j) hrest)
    (by rw [ht]; exact mul_ne_zero (hq j) hrest)
  rw [hf,ht] at he
  exact (mul_right_cancel₀ hrest he)

end Paper2.MatchingPropagation
