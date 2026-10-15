import Paper2.MatchingPropagation.Double

namespace Paper2.MatchingPropagation
open CommonPhase EndpointSelfLoop
variable {ι : Type}

def Forces (F : Tensor ℂ ι) (a b : ι) : Prop :=
  ∀ x, F x ≠ 0 → x b = !(x a)

theorem Forces.symm {F : Tensor ℂ ι} {a b : ι} (h : Forces F a b) : Forces F b a := by
  intro x hx
  have := h x hx
  cases ha : x a <;> cases hb : x b <;> simp_all

theorem mate_injective (P : Matching ι) : Function.Injective (mate P) := by
  intro a b h
  simpa using congrArg (mate P) h

theorem index_eq_iff (P : Matching ι) (a b : ι) :
    (P.ports.symm a).1 = (P.ports.symm b).1 ↔ a = b ∨ a = mate P b := by
  obtain ⟨⟨j,s⟩,rfl⟩ := P.ports.surjective a
  obtain ⟨⟨k,t⟩,rfl⟩ := P.ports.surjective b
  cases s <;> cases t <;> simp [mate]

noncomputable def edgeFlip (P : Matching ι) (j : Fin P.count) (x : ι → Bool) : ι → Bool := by
  classical
  exact fun a => if (P.ports.symm a).1 = j then !(x a) else x a

@[simp] theorem edgeFlip_port (P : Matching ι) (j k : Fin P.count)
    (x : ι → Bool) (b : Bool) :
    edgeFlip P j x (P.ports (k,b)) = if k = j then !(x (P.ports (k,b))) else x (P.ports (k,b)) := by
  classical
  simp [edgeFlip]

theorem edgeFlip_transversal (P : Matching ι) (j : Fin P.count)
    (x : ι → Bool) (hx : Transversal P x) : Transversal P (edgeFlip P j x) := by
  classical
  intro k
  by_cases h : k = j
  · subst k
    simp [hx j]
  · simp [h,hx k]

theorem pairSum_literal_nonzero_of_word (P : Matching ι) (e : PortPair ι)
    (x : ι → Bool) (hx : Transversal P x) (he : x e.second = !(x e.first)) :
    e.pairSum (literal P ℂ) x ≠ 0 := by
  classical
  rw [PortPair.pairSum_eq_loop,loop_apply_restrict _ _ _ _ x he]
  have h₁ : literal P ℂ x = 1 := by simp [literal,hx]
  rw [h₁]
  rcases literal_eq_zero_or_one (K := ℂ) P (fun i => x (Equiv.swap e.first e.second i)) with h | h <;>
    rw [h] <;> norm_num

/-- A supported output of an actual sum has a supported summand. -/
theorem pairSum_support (F : Tensor ℂ ι) (e : PortPair ι) (x : ι → Bool)
    (hx : e.pairSum F x ≠ 0) : ∃ t, F (e.fill x t) ≠ 0 := by
  by_contra h
  push Not at h
  apply hx
  simp [PortPair.pairSum,h]

theorem pairSum_product_forces_mate (P : Matching ι) (p q : Fin P.count → ℂ)
    (c : ℂ) (hc : c ≠ 0) (hp : ∀ j, p j ≠ 0) (hq : ∀ j, q j ≠ 0)
    (e : PortPair ι) (a b : ι) (hab : mate P a = b)
    (ha₁ : a ≠ e.first) (ha₂ : a ≠ e.second)
    (hb₁ : b ≠ e.first) (hb₂ : b ≠ e.second) :
    Forces (e.pairSum (product P p q c)) a b := by
  intro x hx
  obtain ⟨t,ht⟩ := pairSum_support _ e x hx
  have h := (transversal_iff_mate P _).mp ((product_ne_zero P p q c hc hp hq _).mp ht) a
  rw [hab,fill_other e x t b hb₁ hb₂,fill_other e x t a ha₁ ha₂] at h
  exact h

/-- Splicing two matching edges really forces their surviving endpoints opposite. -/
theorem pairSum_product_forces_splice (P : Matching ι) (p q : Fin P.count → ℂ)
    (c : ℂ) (hc : c ≠ 0) (hp : ∀ j, p j ≠ 0) (hq : ∀ j, q j ≠ 0)
    (e : PortPair ι) (a b : ι)
    (ha : mate P a = e.first) (hb : mate P b = e.second)
    (ha₁ : a ≠ e.first) (ha₂ : a ≠ e.second)
    (hb₁ : b ≠ e.first) (hb₂ : b ≠ e.second) :
    Forces (e.pairSum (product P p q c)) a b := by
  intro x hx
  obtain ⟨t,ht⟩ := pairSum_support _ e x hx
  have h := (transversal_iff_mate P _).mp ((product_ne_zero P p q c hc hp hq _).mp ht)
  have h₁ := h a
  have h₂ := h b
  rw [ha,fill_first,fill_other e x t a ha₁ ha₂] at h₁
  rw [hb,fill_second,fill_other e x t b hb₁ hb₂] at h₂
  cases t <;> cases hxa : x a <;> cases hxb : x b <;> simp [hxa,hxb] at h₁ h₂ ⊢

/-- If two unpaired surviving ports become paired, the deleted pair must meet
the first port's mate. The proof flips one independent matching choice. -/
theorem literal_forces_mate_deleted (P : Matching ι) (e : PortPair ι) (a b : ι)
    (hab : a ≠ b) (hm : mate P a ≠ b)
    (ha₁ : a ≠ e.first) (ha₂ : a ≠ e.second)
    (hforce : Forces (e.pairSum (literal P ℂ)) a b) :
    mate P a = e.first ∨ mate P a = e.second := by
  classical
  by_contra hn
  push Not at hn
  let j := (P.ports.symm a).1
  have hba : (P.ports.symm b).1 ≠ j := by
    intro h
    rcases (index_eq_iff P b a).mp h with h | h
    · exact hab h.symm
    · exact hm h.symm
  have he₁ : (P.ports.symm e.first).1 ≠ j := by
    intro h
    rcases (index_eq_iff P e.first a).mp h with h | h
    · exact ha₁ h.symm
    · exact hn.1 h.symm
  have he₂ : (P.ports.symm e.second).1 ≠ j := by
    intro h
    rcases (index_eq_iff P e.second a).mp h with h | h
    · exact ha₂ h.symm
    · exact hn.2 h.symm
  obtain ⟨x,hx,he⟩ := exists_literal_opposite (K := ℂ) P e.first e.second e.distinct
  have htx : Transversal P x := by
    by_contra ht
    simp [literal,ht] at hx
  have hf₁ := hforce x (pairSum_literal_nonzero_of_word P e x htx he)
  have he' : edgeFlip P j x e.second = !(edgeFlip P j x e.first) := by
    simpa only [edgeFlip,if_neg he₁,if_neg he₂] using he
  have hf₂ := hforce (edgeFlip P j x)
    (pairSum_literal_nonzero_of_word P e _ (edgeFlip_transversal P j x htx) he')
  simp only [edgeFlip,if_neg hba,if_pos rfl,Bool.not_not] at hf₂
  have hxaa : (P.ports.symm a).1 = j := rfl
  simp only [edgeFlip,if_neg hba,if_pos hxaa,Bool.not_not] at hf₂
  cases hxa : x a <;> cases hxb : x b <;> simp_all

/-- Exact support obstruction used by condition 2: only deleting the two mates
can splice previously distinct edges into the named surviving pair. -/
theorem literal_forces_deleted_mates (P : Matching ι) (e : PortPair ι) (a b : ι)
    (hab : a ≠ b) (hm : mate P a ≠ b)
    (ha₁ : a ≠ e.first) (ha₂ : a ≠ e.second)
    (hb₁ : b ≠ e.first) (hb₂ : b ≠ e.second)
    (hforce : Forces (e.pairSum (literal P ℂ)) a b) :
    (mate P a = e.first ∧ mate P b = e.second) ∨
      (mate P a = e.second ∧ mate P b = e.first) := by
  have hm' : mate P b ≠ a := by
    intro h
    apply hm
    simpa using congrArg (mate P) h.symm
  have ha := literal_forces_mate_deleted P e a b hab hm ha₁ ha₂ hforce
  have hb := literal_forces_mate_deleted P e b a hab.symm hm' hb₁ hb₂ hforce.symm
  have hne : mate P a ≠ mate P b := fun h => hab (mate_injective P h)
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact False.elim (hne (ha.trans hb.symm))
  · exact Or.inl ⟨ha,hb⟩
  · exact Or.inr ⟨ha,hb⟩
  · exact False.elim (hne (ha.trans hb.symm))

end Paper2.MatchingPropagation
