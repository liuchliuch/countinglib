import Paper2.HeightOne.Cyclic.Origin

/-! The supported weight-two graph is an actual matching, and each edge
forces equality on the whole original tensor support. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open EndpointSelfLoop
variable {K : Type*} [Field K]

lemma exists_two_avoiding_three {n : ℕ} (hn : 5 ≤ n) (u v w : Fin n) :
    ∃ a b : Fin n, a ≠ b ∧ a ≠ u ∧ a ≠ v ∧ a ≠ w ∧ b ≠ u ∧ b ≠ v ∧ b ≠ w := by
  classical
  let S : Finset (Fin n) := {u, v, w}
  have hS : S.card ≤ 3 := by
    have h1 := Finset.card_insert_le u ({v, w} : Finset (Fin n))
    have h2 := Finset.card_insert_le v ({w} : Finset (Fin n))
    have h3 : ({w} : Finset (Fin n)).card = 1 := Finset.card_singleton w
    dsimp only [S]
    omega
  have hcard : 1 < (Finset.univ \ S).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  have ha' : a ≠ u ∧ a ≠ v ∧ a ≠ w := by simpa [S] using (Finset.mem_sdiff.mp ha).2
  have hb' : b ≠ u ∧ b ≠ v ∧ b ≠ w := by simpa [S] using (Finset.mem_sdiff.mp hb).2
  exact ⟨a, b, hab, ha'.1, ha'.2.1, ha'.2.2, hb'.1, hb'.2.1, hb'.2.2⟩

lemma matching_code_pair_constraint {n : ℕ} (P : Pairing n) (u v : Fin n) (huv : u ≠ v)
    (he : weightTwoWord u v ∈ equalityCode P) (x : Fin n → Bool)
    (hx : x ∈ equalityCode P) : x u = x v := by
  have hm := (weightTwoWord_mem_iff P u v huv).mp he
  have h := (mem_equalityCode_iff_mate P x).mp hx u
  rw [hm] at h
  exact h.symm

/-- Two supported weight-two edges cannot have a common endpoint. -/
theorem weightTwo_unique_partner {n : ℕ} (f : Signature K n) (hf : f ≠ 0)
    (hn : 5 ≤ n) (S : Set K)
    (hthree : ∃ s ∈ S, ∃ t ∈ S, ∃ z ∈ S, s ≠ t ∧ s ≠ z ∧ t ≠ z)
    (hcards : ∀ a b (hab : a ≠ b), ∀ q ∈ S, plusContraction a b hab q f ≠ 0 →
      EqualityMatchingSupport (plusContraction a b hab q f))
    (u v w : Fin n) (huv : u ≠ v) (huw : u ≠ w)
    (hv : f (pairWord u v) ≠ 0) (hw : f (pairWord u w) ≠ 0) : v = w := by
  classical
  obtain ⟨a, b, hab, hau, hav, haw, hbu, hbv, hbw⟩ := exists_two_avoiding_three hn u v w
  obtain ⟨s, hs, t, ht, z, hz, hst, hsz, htz⟩ := hthree
  have hvis := matching_cards_visible f hf (by simpa using hn) S s t hs ht hst hcards a b hab
  obtain ⟨P, hP⟩ := common_matching_projection f S
    ⟨s, hs, t, ht, z, hz, hst, hsz, htz⟩ a b hab (hcards a b hab)
    (hvis.elim (fun h => ⟨s, hs, h⟩) (fun h => ⟨t, ht, h⟩))
  let u' : Remaining a b := ⟨u, Ne.symm hau, Ne.symm hbu⟩
  let v' : Remaining a b := ⟨v, Ne.symm hav, Ne.symm hbv⟩
  let w' : Remaining a b := ⟨w, Ne.symm haw, Ne.symm hbw⟩
  let e := Fintype.equivFin (Remaining a b)
  have hv' : weightTwoWord (e u') (e v') ∈ equalityCode P := by
    have h := hP (pairWord u v) hv (by simp [pairWord, hau, hav, hbu, hbv])
    change (fun j => pairWord u'.val v'.val (e.symm j).val) ∈ equalityCode P at h
    rwa [pairWord_projected] at h
  have hw' : weightTwoWord (e u') (e w') ∈ equalityCode P := by
    have h := hP (pairWord u w) hw (by simp [pairWord, hau, haw, hbu, hbw])
    change (fun j => pairWord u'.val w'.val (e.symm j).val) ∈ equalityCode P at h
    rwa [pairWord_projected] at h
  have hvw := supported_weightTwo_unique_partner P (e u') (e v') (e w')
    (fun h => huv (congrArg Subtype.val (e.injective h)))
    (fun h => huw (congrArg Subtype.val (e.injective h))) hv' hw'
  exact congrArg Subtype.val (e.injective hvw)

/-- Every supported weight-two edge is a global equality constraint. -/
theorem weightTwo_forces_equality {n : ℕ} (f : Signature K n) (hf : f ≠ 0)
    (hn : 5 ≤ n) (S : Set K)
    (hthree : ∃ s ∈ S, ∃ t ∈ S, ∃ z ∈ S, s ≠ t ∧ s ≠ z ∧ t ≠ z)
    (hcards : ∀ a b (hab : a ≠ b), ∀ q ∈ S, plusContraction a b hab q f ≠ 0 →
      EqualityMatchingSupport (plusContraction a b hab q f))
    (u v : Fin n) (huv : u ≠ v) (huvF : f (pairWord u v) ≠ 0) :
    ∀ x, f x ≠ 0 → x u = x v := by
  classical
  intro x hx
  have hrem := remaining_card u v huv
  obtain ⟨a, b, hab, hbits⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Remaining u v => x k.val) (by simp only [Fintype.card_bool, Fintype.card_fin] at *; omega)
  have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  obtain ⟨s, hs, t, ht, z, hz, hst, hsz, htz⟩ := hthree
  have hvis := matching_cards_visible f hf (by simpa using hn) S s t hs ht hst hcards a.val b.val hab'
  obtain ⟨P, hP⟩ := common_matching_projection f S
    ⟨s, hs, t, ht, z, hz, hst, hsz, htz⟩ a.val b.val hab' (hcards a.val b.val hab')
    (hvis.elim (fun h => ⟨s, hs, h⟩) (fun h => ⟨t, ht, h⟩))
  let u' : Remaining a.val b.val := ⟨u, Ne.symm a.property.1, Ne.symm b.property.1⟩
  let v' : Remaining a.val b.val := ⟨v, Ne.symm a.property.2, Ne.symm b.property.2⟩
  let e := Fintype.equivFin (Remaining a.val b.val)
  have hedge : weightTwoWord (e u') (e v') ∈ equalityCode P := by
    have h := hP (pairWord u v) huvF (by simp [pairWord, a.property.1, a.property.2, b.property.1, b.property.2])
    change (fun j => pairWord u'.val v'.val (e.symm j).val) ∈ equalityCode P at h
    rwa [pairWord_projected] at h
  have h := matching_code_pair_constraint P (e u') (e v')
    (fun h => huv (congrArg Subtype.val (e.injective h))) hedge _ (hP x hx hbits)
  simpa only [e, Equiv.symm_apply_apply] using h

end
end Paper2.HeightOne.Cyclic
