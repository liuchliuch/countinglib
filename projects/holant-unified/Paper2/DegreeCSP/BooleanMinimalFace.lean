import Paper2.DegreeCSP.BooleanQuadratic

/-! A nonzero Boolean sign with vanishing constant and singleton values has a
literal two-coordinate AND face. The witness comes from a smallest true
support, so all three proper corners are exactly zero. -/
namespace Paper2.DegreeCSP.BooleanMinimalFace

open Holant.Tractable.AffinePhase (Word origin word)

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

private theorem singleton_word (i : Fin n) :
    word ({i} : Finset (Fin n)) = Function.update (origin n) i true := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp [word]
  · simp [word, origin, Function.update, h]

private theorem update_erase (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    Function.update (word (S.erase i)) i true = word S := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp [word, hi]
  · simp [word, Function.update, h]

private theorem update_false (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    Function.update (word S) i false = word S := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp [word, hi]
  · simp [Function.update, h]

theorem exists_and_face (P : Word n → ZMod 2)
    (hzero : P (origin n) = 0)
    (hsingle : ∀ i : Fin n, P (Function.update (origin n) i true) = 0)
    (hex : ∃ x, P x = 1) :
    ∃ z i j, i ≠ j ∧ ∀ b c : Bool,
      P (Function.update (Function.update z i b) j c) =
        if b && c then 1 else 0 := by
  classical
  have finite : ∃ k : ℕ, ∃ S : Finset (Fin n), P (word S) = 1 ∧ S.card = k := by
    obtain ⟨x, hx⟩ := hex
    let S : Finset (Fin n) := Finset.univ.filter (fun i => x i = true)
    have hw : word S = x := by
      funext i
      simp [word, S]
    exact ⟨S.card, S, hw ▸ hx, rfl⟩
  obtain ⟨S, hP, hcard⟩ := Nat.find_spec finite
  have hmin (T : Finset (Fin n)) (hlt : T.card < S.card) : P (word T) = 0 := by
    by_contra hn
    have hone : P (word T) = 1 := by
      generalize hval : P (word T) = a at hn ⊢
      fin_cases a
      · exact (hn rfl).elim
      · rfl
    have least := Nat.find_min' finite (show ∃ U : Finset (Fin n),
        P (word U) = 1 ∧ U.card = T.card from ⟨T, hone, rfl⟩)
    omega
  have htwo : 1 < S.card := by
    by_contra hn
    have hc : S.card ≤ 1 := Nat.le_of_not_gt hn
    have cases : S.card = 0 ∨ S.card = 1 := by omega
    rcases cases with hc0 | hc1
    · have he : S = ∅ := Finset.card_eq_zero.mp hc0
      subst S
      simp only [Holant.Tractable.AffinePhase.word_empty, hzero] at hP
      exact zero_ne_one hP
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc1
      subst S
      rw [singleton_word, hsingle] at hP
      exact zero_ne_one hP
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp htwo
  let T := (S.erase i).erase j
  have hiT : i ∉ T := by simp [T]
  have hjT : j ∉ T := by simp [T]
  have hjEi : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hiEj : i ∈ S.erase j := Finset.mem_erase.mpr ⟨hij, hi⟩
  have hTj : T = (S.erase j).erase i := by
    ext k
    simp [T, and_left_comm]
  have hjEj : j ∉ S.erase j := by simp
  have h00 : P (word T) = 0 := hmin T
    (lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hi))
  have h01 : P (word (S.erase i)) = 0 :=
    hmin (S.erase i) (Finset.card_erase_lt_of_mem hi)
  have h10 : P (word (S.erase j)) = 0 :=
    hmin (S.erase j) (Finset.card_erase_lt_of_mem hj)
  refine ⟨word T, i, j, hij, ?_⟩
  intro b c
  cases b <;> cases c
  · rw [update_false T i hiT, update_false T j hjT, h00]
    rfl
  · rw [update_false T i hiT, update_erase (S.erase i) j hjEi, h01]
    rfl
  · rw [hTj, update_erase (S.erase j) i hiEj,
      update_false (S.erase j) j hjEj, h10]
    rfl
  · rw [hTj, update_erase (S.erase j) i hiEj, update_erase S j hj, hP]
    rfl

end
end Paper2.DegreeCSP.BooleanMinimalFace
