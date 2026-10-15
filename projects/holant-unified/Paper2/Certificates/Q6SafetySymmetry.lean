import Paper2.Certificates.Q6Sparse

/-! Reindexing principles for the necessary quaternary equations. These are
algebraic statements about the three complementary pairs of W₄ entries. -/
namespace Paper2.Certificates.Q6

variable {K : Type*} [CommRing K] [NoZeroDivisors K]

def entryComplement : Fin 6 → Fin 6 := ![5,4,3,2,1,0]

/-- An orientation-free presentation of Q6.6--Q6.7. -/
def SymmetricSafe (v : Fin 6 → K) : Prop :=
  (∀ i, v i = 0 ↔ v (entryComplement i) = 0) ∧
  (∃ i, v i = 0) ∧
  ∀ i j, v i * v (entryComplement i) = 0 ∨
    v j * v (entryComplement j) = 0 ∨
    (v i * v (entryComplement i))^2 = (v j * v (entryComplement j))^2

theorem NecessarySafe.symmetric {v : Fin 6 → K} (h : NecessarySafe v) : SymmetricSafe v := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact h.zero05
    · exact h.zero14
    · exact h.zero23
    · exact h.zero23.symm
    · exact h.zero14.symm
    · exact h.zero05.symm
  · rcases h.zeroProduct with h0 | h0 | h0
    · rcases mul_eq_zero.mp h0 with h0 | h0
      · exact ⟨0,h0⟩
      · exact ⟨5,h0⟩
    · rcases mul_eq_zero.mp h0 with h0 | h0
      · exact ⟨1,h0⟩
      · exact ⟨4,h0⟩
    · rcases mul_eq_zero.mp h0 with h0 | h0
      · exact ⟨2,h0⟩
      · exact ⟨3,h0⟩
  · intro i j
    have h10 : v 1*v 4=0 ∨ v 0*v 5=0 ∨ (v 1*v 4)^2=(v 0*v 5)^2 := by
      rcases h.products01 with hz | hz | hz
      · exact Or.inr (Or.inl hz)
      · exact Or.inl hz
      · exact Or.inr (Or.inr hz.symm)
    have h20 : v 2*v 3=0 ∨ v 0*v 5=0 ∨ (v 2*v 3)^2=(v 0*v 5)^2 := by
      rcases h.products02 with hz | hz | hz
      · exact Or.inr (Or.inl hz)
      · exact Or.inl hz
      · exact Or.inr (Or.inr hz.symm)
    have h21 : v 2*v 3=0 ∨ v 1*v 4=0 ∨ (v 2*v 3)^2=(v 1*v 4)^2 := by
      rcases h.products12 with hz | hz | hz
      · exact Or.inr (Or.inl hz)
      · exact Or.inl hz
      · exact Or.inr (Or.inr hz.symm)
    fin_cases i <;> fin_cases j
    · change v 0 * v 5 = 0 ∨ v 0 * v 5 = 0 ∨ (v 0 * v 5)^2 = (v 0 * v 5)^2
      exact Or.inr (Or.inr (by simp only [mul_comm]))
    · change v 0 * v 5 = 0 ∨ v 1 * v 4 = 0 ∨ (v 0 * v 5)^2 = (v 1 * v 4)^2
      simpa only [mul_comm] using h.products01
    · change v 0 * v 5 = 0 ∨ v 2 * v 3 = 0 ∨ (v 0 * v 5)^2 = (v 2 * v 3)^2
      simpa only [mul_comm] using h.products02
    · change v 0 * v 5 = 0 ∨ v 3 * v 2 = 0 ∨ (v 0 * v 5)^2 = (v 3 * v 2)^2
      simpa only [mul_comm] using h.products02
    · change v 0 * v 5 = 0 ∨ v 4 * v 1 = 0 ∨ (v 0 * v 5)^2 = (v 4 * v 1)^2
      simpa only [mul_comm] using h.products01
    · change v 0 * v 5 = 0 ∨ v 5 * v 0 = 0 ∨ (v 0 * v 5)^2 = (v 5 * v 0)^2
      exact Or.inr (Or.inr (by simp only [mul_comm]))
    · change v 1 * v 4 = 0 ∨ v 0 * v 5 = 0 ∨ (v 1 * v 4)^2 = (v 0 * v 5)^2
      simpa only [mul_comm] using h10
    · change v 1 * v 4 = 0 ∨ v 1 * v 4 = 0 ∨ (v 1 * v 4)^2 = (v 1 * v 4)^2
      exact Or.inr (Or.inr (by simp only [mul_comm]))
    · change v 1 * v 4 = 0 ∨ v 2 * v 3 = 0 ∨ (v 1 * v 4)^2 = (v 2 * v 3)^2
      simpa only [mul_comm] using h.products12
    · change v 1 * v 4 = 0 ∨ v 3 * v 2 = 0 ∨ (v 1 * v 4)^2 = (v 3 * v 2)^2
      simpa only [mul_comm] using h.products12
    · change v 1 * v 4 = 0 ∨ v 4 * v 1 = 0 ∨ (v 1 * v 4)^2 = (v 4 * v 1)^2
      exact Or.inr (Or.inr (by simp only [mul_comm]))
    · change v 1 * v 4 = 0 ∨ v 5 * v 0 = 0 ∨ (v 1 * v 4)^2 = (v 5 * v 0)^2
      simpa only [mul_comm] using h10
    · change v 2 * v 3 = 0 ∨ v 0 * v 5 = 0 ∨ (v 2 * v 3)^2 = (v 0 * v 5)^2
      simpa only [mul_comm] using h20
    · change v 2 * v 3 = 0 ∨ v 1 * v 4 = 0 ∨ (v 2 * v 3)^2 = (v 1 * v 4)^2
      simpa only [mul_comm] using h21
    · change v 2 * v 3 = 0 ∨ v 2 * v 3 = 0 ∨ (v 2 * v 3)^2 = (v 2 * v 3)^2
      exact Or.inr (Or.inr (by simp only [mul_comm]))
    · change v 2 * v 3 = 0 ∨ v 3 * v 2 = 0 ∨ (v 2 * v 3)^2 = (v 3 * v 2)^2
      exact Or.inr (Or.inr (by simp only [mul_comm]))
    · change v 2 * v 3 = 0 ∨ v 4 * v 1 = 0 ∨ (v 2 * v 3)^2 = (v 4 * v 1)^2
      simpa only [mul_comm] using h21
    · change v 2 * v 3 = 0 ∨ v 5 * v 0 = 0 ∨ (v 2 * v 3)^2 = (v 5 * v 0)^2
      simpa only [mul_comm] using h20
    · change v 3 * v 2 = 0 ∨ v 0 * v 5 = 0 ∨ (v 3 * v 2)^2 = (v 0 * v 5)^2
      simpa only [mul_comm] using h20
    · change v 3 * v 2 = 0 ∨ v 1 * v 4 = 0 ∨ (v 3 * v 2)^2 = (v 1 * v 4)^2
      simpa only [mul_comm] using h21
    · change v 3 * v 2 = 0 ∨ v 2 * v 3 = 0 ∨ (v 3 * v 2)^2 = (v 2 * v 3)^2
      exact Or.inr (Or.inr (by simp only [mul_comm]))
    · change v 3 * v 2 = 0 ∨ v 3 * v 2 = 0 ∨ (v 3 * v 2)^2 = (v 3 * v 2)^2
      exact Or.inr (Or.inr (by simp only [mul_comm]))
    · change v 3 * v 2 = 0 ∨ v 4 * v 1 = 0 ∨ (v 3 * v 2)^2 = (v 4 * v 1)^2
      simpa only [mul_comm] using h21
    · change v 3 * v 2 = 0 ∨ v 5 * v 0 = 0 ∨ (v 3 * v 2)^2 = (v 5 * v 0)^2
      simpa only [mul_comm] using h20
    · change v 4 * v 1 = 0 ∨ v 0 * v 5 = 0 ∨ (v 4 * v 1)^2 = (v 0 * v 5)^2
      simpa only [mul_comm] using h10
    · change v 4 * v 1 = 0 ∨ v 1 * v 4 = 0 ∨ (v 4 * v 1)^2 = (v 1 * v 4)^2
      exact Or.inr (Or.inr (by simp only [mul_comm]))
    · change v 4 * v 1 = 0 ∨ v 2 * v 3 = 0 ∨ (v 4 * v 1)^2 = (v 2 * v 3)^2
      simpa only [mul_comm] using h.products12
    · change v 4 * v 1 = 0 ∨ v 3 * v 2 = 0 ∨ (v 4 * v 1)^2 = (v 3 * v 2)^2
      simpa only [mul_comm] using h.products12
    · change v 4 * v 1 = 0 ∨ v 4 * v 1 = 0 ∨ (v 4 * v 1)^2 = (v 4 * v 1)^2
      exact Or.inr (Or.inr (by simp only [mul_comm]))
    · change v 4 * v 1 = 0 ∨ v 5 * v 0 = 0 ∨ (v 4 * v 1)^2 = (v 5 * v 0)^2
      simpa only [mul_comm] using h10
    · change v 5 * v 0 = 0 ∨ v 0 * v 5 = 0 ∨ (v 5 * v 0)^2 = (v 0 * v 5)^2
      exact Or.inr (Or.inr (by simp only [mul_comm]))
    · change v 5 * v 0 = 0 ∨ v 1 * v 4 = 0 ∨ (v 5 * v 0)^2 = (v 1 * v 4)^2
      simpa only [mul_comm] using h.products01
    · change v 5 * v 0 = 0 ∨ v 2 * v 3 = 0 ∨ (v 5 * v 0)^2 = (v 2 * v 3)^2
      simpa only [mul_comm] using h.products02
    · change v 5 * v 0 = 0 ∨ v 3 * v 2 = 0 ∨ (v 5 * v 0)^2 = (v 3 * v 2)^2
      simpa only [mul_comm] using h.products02
    · change v 5 * v 0 = 0 ∨ v 4 * v 1 = 0 ∨ (v 5 * v 0)^2 = (v 4 * v 1)^2
      simpa only [mul_comm] using h.products01
    · change v 5 * v 0 = 0 ∨ v 5 * v 0 = 0 ∨ (v 5 * v 0)^2 = (v 5 * v 0)^2
      exact Or.inr (Or.inr (by simp only [mul_comm]))

/-- No nonzero assumption is needed on the boundary array. -/
theorem SymmetricSafe.necessary {v : Fin 6 → K} (h : SymmetricSafe v) : NecessarySafe v := by
  refine ⟨h.1 0,h.1 1,h.1 2,?_,h.2.2 0 1,h.2.2 0 2,h.2.2 1 2⟩
  obtain ⟨i,hi⟩ := h.2.1
  fin_cases i
  · exact Or.inl (mul_eq_zero.mpr (Or.inl hi))
  · exact Or.inr (Or.inl (mul_eq_zero.mpr (Or.inl hi)))
  · exact Or.inr (Or.inr (mul_eq_zero.mpr (Or.inl hi)))
  · exact Or.inr (Or.inr (mul_eq_zero.mpr (Or.inr hi)))
  · exact Or.inr (Or.inl (mul_eq_zero.mpr (Or.inr hi)))
  · exact Or.inl (mul_eq_zero.mpr (Or.inr hi))

theorem NecessarySafe.reindex {v : Fin 6 → K} (h : NecessarySafe v)
    (p : Equiv.Perm (Fin 6))
    (hp : ∀ i, p (entryComplement i) = entryComplement (p i)) :
    NecessarySafe (fun i => v (p i)) := by
  have hs := h.symmetric
  apply SymmetricSafe.necessary
  refine ⟨?_, ?_, ?_⟩
  · intro i
    dsimp only
    rw [hp i]
    exact hs.1 (p i)
  · obtain ⟨i,hi⟩ := hs.2.1
    refine ⟨p.symm i, ?_⟩
    simpa only [p.apply_symm_apply] using hi
  · intro i j
    dsimp only
    rw [hp i,hp j]
    exact hs.2.2 (p i) (p j)

def entryComplementEquiv : Equiv.Perm (Fin 6) where
  toFun := entryComplement
  invFun := entryComplement
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem NecessarySafe.complement {v : Fin 6 → K} (h : NecessarySafe v) :
    NecessarySafe (fun e => v (entryComplement e)) :=
  h.reindex entryComplementEquiv (fun _ => rfl)

end Paper2.Certificates.Q6
