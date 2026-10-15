import Paper2.HeightOne.Cyclic.MatchingCore

/-! Actual named-port geometry of closing first endpoints from two distinct
matching edges. The common-bit diagonal cube has exactly the card-support size. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open EndpointSelfLoop

abbrev blockWord {n : ℕ} (P : Pairing n) (t : Fin P.count → Bool) : Fin n → Bool :=
  fun k => t (P.ports.symm k).1

@[simp] lemma blockWord_port {n : ℕ} (P : Pairing n) (t : Fin P.count → Bool)
    (i : Fin P.count) (b : Bool) : blockWord P t (P.ports (i, b)) = t i := by simp [blockWord]

lemma blockWord_mem {n : ℕ} (P : Pairing n) (t : Fin P.count → Bool) :
    blockWord P t ∈ equalityCode P := by
  rw [mem_equalityCode]
  intro i
  exact (blockWord_port P t i false).trans (blockWord_port P t i true).symm

lemma reconstruct_blockWord {n : ℕ} (P : Pairing n) (x : Fin n → Bool)
    (hx : x ∈ equalityCode P) : blockWord P (fun i => x (P.ports (i, false))) = x := by
  funext k
  obtain ⟨⟨i, b⟩, rfl⟩ := P.ports.surjective k
  cases b
  · simp
  · simpa using (mem_equalityCode P x).mp hx i

abbrev diagonalWords {r : ℕ} (i j : Fin r) := {t : Fin r → Bool // t i = t j}

instance {r : ℕ} (i j : Fin r) : Fintype (diagonalWords i j) := by
  classical
  exact Subtype.fintype _

def diagonalWordsEquiv {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    diagonalWords i j ≃ ({k : Fin r // k ≠ j} → Bool) where
  toFun t k := t.val k.val
  invFun t := ⟨fun k => if hk : k = j then t ⟨i, hij⟩ else t ⟨k, hk⟩, by simp [hij]⟩
  left_inv t := by
    apply Subtype.ext
    funext k
    by_cases hk : k = j
    · subst k
      simp only [dite_eq_ite, if_pos rfl]
      exact t.property
    · simp [hk]
  right_inv t := by
    funext k
    simp [k.property]

lemma diagonalWords_card {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    Fintype.card (diagonalWords i j) = 2 ^ (r - 1) := by
  classical
  rw [Fintype.card_congr (diagonalWordsEquiv i j hij), Fintype.card_fun, Fintype.card_bool]
  congr 1
  have h := Fintype.card_subtype_compl (p := fun k : Fin r => k = j)
  have he : Fintype.card {k : Fin r // k = j} = 1 := by simp
  simp only [Fintype.card_fin, he] at h
  omega

abbrev crossRemaining {n : ℕ} (P : Pairing n) (i j : Fin P.count) :=
  Remaining (P.ports (i, false)) (P.ports (j, false))

lemma cross_distinct {n : ℕ} (P : Pairing n) (i j : Fin P.count) (hij : i ≠ j) :
    P.ports (i, false) ≠ P.ports (j, false) := by simpa using hij

def residualBlockWord {n : ℕ} (P : Pairing n) (i j : Fin P.count)
    (t : Fin P.count → Bool) : Fin (Fintype.card (crossRemaining P i j)) → Bool :=
  fun k => blockWord P t ((Fintype.equivFin (crossRemaining P i j)).symm k).val

def retainedSecond {n : ℕ} (P : Pairing n) (i j k : Fin P.count) : crossRemaining P i j :=
  ⟨P.ports (k, true), by simp, by simp⟩

@[simp] lemma residualBlockWord_second {n : ℕ} (P : Pairing n) (i j k : Fin P.count)
    (t : Fin P.count → Bool) :
    residualBlockWord P i j t ((Fintype.equivFin (crossRemaining P i j)) (retainedSecond P i j k)) = t k := by
  simp only [residualBlockWord, Equiv.symm_apply_apply, retainedSecond]
  exact blockWord_port P t k true

lemma residualBlockWord_injective {n : ℕ} (P : Pairing n) (i j : Fin P.count) :
    Function.Injective (residualBlockWord P i j) := by
  intro x y h
  funext k
  simpa only [residualBlockWord_second] using congrFun h
    ((Fintype.equivFin (crossRemaining P i j)) (retainedSecond P i j k))

def crossCode {n : ℕ} (P : Pairing n) (i j : Fin P.count) :
    Finset (Fin (Fintype.card (crossRemaining P i j)) → Bool) := by
  classical
  exact Finset.univ.image (fun t : diagonalWords i j => residualBlockWord P i j t.val)

lemma mem_crossCode {n : ℕ} (P : Pairing n) (i j : Fin P.count)
    (x : Fin (Fintype.card (crossRemaining P i j)) → Bool) :
    x ∈ crossCode P i j ↔ ∃ t, t i = t j ∧ residualBlockWord P i j t = x := by
  classical
  simp only [crossCode, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t.val, t.property, ht⟩
  · rintro ⟨t, ht, he⟩
    exact ⟨⟨t, ht⟩, he⟩

lemma crossCode_card {n : ℕ} (P : Pairing n) (i j : Fin P.count) (hij : i ≠ j) :
    (crossCode P i j).card = 2 ^ (Fintype.card (crossRemaining P i j) / 2) := by
  classical
  rw [crossCode, Finset.card_image_of_injective _ (fun x y h => Subtype.ext (residualBlockWord_injective P i j h)),
    Finset.card_univ, diagonalWords_card i j hij]
  congr 1
  have hn := Matching.pair_count P
  have hm := remaining_card (P.ports (i, false)) (P.ports (j, false)) (cross_distinct P i j hij)
  simp only [Fintype.card_fin] at hm
  change Fintype.card (crossRemaining P i j) + 2 = n at hm
  omega

end
end Paper2.HeightOne.Cyclic
