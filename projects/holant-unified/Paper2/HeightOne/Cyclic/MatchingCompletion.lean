import Paper2.HeightOne.Cyclic.WeightTwo

/-! A matching-completion lemma on the original ports. Deleting one endpoint
of an existing edge and any other port leaves a genuine perfect matching;
all residual edges away from the other endpoint must be original edges. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open EndpointSelfLoop

structure FreeMatching (ι : Type) where
  mate : ι → ι
  involutive : Function.Involutive mate
  ne : ∀ i, mate i ≠ i

lemma FreeMatching.injective {ι : Type} (M : FreeMatching ι) : Function.Injective M.mate :=
  M.involutive.injective

def remainingMatching {n : ℕ} {a b : Fin n} (P : Pairing (Fintype.card (Remaining a b))) :
    FreeMatching (Remaining a b) where
  mate x := (Fintype.equivFin (Remaining a b)).symm (pairingMate P ((Fintype.equivFin (Remaining a b)) x))
  involutive x := by simp
  ne x h := by
    have he := congrArg (Fintype.equivFin (Remaining a b)) h
    simpa using he

lemma exists_outside_two {ι : Type} [Fintype ι] (hcard : 3 ≤ Fintype.card ι) (u v : ι) :
    ∃ k, k ≠ u ∧ k ≠ v := by
  classical
  let S : Finset ι := {u, v}
  have hS : S.card ≤ 2 := by
    have h := Finset.card_insert_le u ({v} : Finset ι)
    simp only [Finset.card_singleton] at h
    exact h
  have hc : 0 < (Finset.univ \ S).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hc
  exact ⟨k, by simpa [S] using (Finset.mem_sdiff.mp hk).2⟩

/-- A nonempty matching with these deleted-pair completions has no unmatched
original vertex. This is a finite graph statement, independent of coefficients. -/
theorem matching_relation_is_perfect {n : ℕ} (hn : 6 ≤ n)
    (R : Fin n → Fin n → Prop) (hsymm : Symmetric R) (hirr : ∀ u, ¬ R u u)
    (hunique : ∀ u v w, R u v → R u w → v = w)
    (u v : Fin n) (huv : R u v)
    (hdeck : ∀ k, k ≠ u → k ≠ v → ∃ M : FreeMatching (Remaining u k),
      ∀ p, p.val ≠ v → (M.mate p).val ≠ v → R p.val (M.mate p).val) :
    ∀ x, ∃ y, R x y := by
  classical
  have huvne : u ≠ v := by
    intro h
    subst v
    exact hirr u huv
  obtain ⟨k, hku, hkv⟩ := exists_outside_two (by simpa using (show 3 ≤ n by omega)) u v
  obtain ⟨M, hM⟩ := hdeck k hku hkv
  let v' : Remaining u k := ⟨v, Ne.symm huvne, Ne.symm hkv⟩
  have hrem : 3 ≤ Fintype.card (Remaining u k) := by
    have h := remaining_card u k (Ne.symm hku)
    simp only [Fintype.card_fin] at h
    omega
  obtain ⟨p, hpv, hpm⟩ := exists_outside_two hrem v' (M.mate v')
  have hpv' : p.val ≠ v := fun h => hpv (Subtype.ext h)
  have hmpv : (M.mate p).val ≠ v := by
    intro h
    have he : M.mate p = v' := Subtype.ext h
    have hh := congrArg M.mate he
    rw [M.involutive p] at hh
    exact hpm hh
  have hpq : R p.val (M.mate p).val := hM p hpv' hmpv
  let a := p.val
  let b := (M.mate p).val
  have hau : a ≠ u := p.property.1
  have hav : a ≠ v := hpv'
  have hbu : b ≠ u := (M.mate p).property.1
  have hbv : b ≠ v := hmpv
  have hab : a ≠ b := fun h => M.ne p (Subtype.ext h.symm)
  obtain ⟨Q, hQ⟩ := hdeck a hau hav
  let v'' : Remaining u a := ⟨v, Ne.symm huvne, Ne.symm hav⟩
  let b' : Remaining u a := ⟨b, hbu, Ne.symm hab⟩
  have hbm : (Q.mate b').val = v := by
    by_contra h
    have hr := hQ b' hbv h
    have he := hunique b a (Q.mate b').val (hsymm hpq) hr
    exact (Q.mate b').property.2 he.symm
  have hbm' : Q.mate b' = v'' := Subtype.ext hbm
  intro x
  by_cases hxu : x = u
  · subst x
    exact ⟨v, huv⟩
  by_cases hxv : x = v
  · subst x
    exact ⟨u, hsymm huv⟩
  by_cases hxa : x = a
  · subst x
    exact ⟨b, hpq⟩
  by_cases hxb : x = b
  · subst x
    exact ⟨a, hsymm hpq⟩
  let x' : Remaining u a := ⟨x, hxu, hxa⟩
  have hmxv : (Q.mate x').val ≠ v := by
    intro h
    have he : Q.mate x' = Q.mate b' := (Subtype.ext h).trans hbm'.symm
    exact hxb (congrArg Subtype.val (Q.injective he))
  exact ⟨(Q.mate x').val, hQ x' hxv hmxv⟩

end
end Paper2.HeightOne.Cyclic
