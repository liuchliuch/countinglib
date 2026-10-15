import Paper2.HeightOne.Cyclic.MatchingSupport

/-! The weight-two words of a literal equality matching code are exactly its
edges. In particular, two supported edges with a common endpoint coincide.
These are statements about the original named residual ports, not a chosen
normal form or a hypothesized common support graph. -/
namespace Paper2.HeightOne.Cyclic
noncomputable section

def pairingMate {n : ℕ} (P : Pairing n) (u : Fin n) : Fin n :=
  P.ports ((P.ports.symm u).1, !(P.ports.symm u).2)

@[simp] theorem pairingMate_port {n : ℕ} (P : Pairing n)
    (j : Fin P.count) (b : Bool) :
    pairingMate P (P.ports (j, b)) = P.ports (j, !b) := by
  simp [pairingMate]

@[simp] theorem pairingMate_pairingMate {n : ℕ} (P : Pairing n) (u : Fin n) :
    pairingMate P (pairingMate P u) = u := by
  simp [pairingMate]

@[simp] theorem pairingMate_ne {n : ℕ} (P : Pairing n) (u : Fin n) :
    pairingMate P u ≠ u := by
  obtain ⟨⟨j, b⟩, rfl⟩ := P.ports.surjective u
  simp only [pairingMate_port, ne_eq, Equiv.apply_eq_iff_eq, Prod.mk.injEq, true_and]
  cases b <;> decide

theorem mem_equalityCode_iff_mate {n : ℕ} (P : Pairing n) (x : Word (Fin n)) :
    x ∈ equalityCode P ↔ ∀ u, x (pairingMate P u) = x u := by
  rw [mem_equalityCode]
  constructor
  · intro h u
    obtain ⟨⟨j, b⟩, rfl⟩ := P.ports.surjective u
    cases b
    · simpa using (h j).symm
    · simpa using h j
  · intro h j
    simpa using h (P.ports (j, true))

/-- The literal indicator of two designated ports. -/
def weightTwoWord {n : ℕ} (u v : Fin n) : Word (Fin n) :=
  fun k => decide (k = u ∨ k = v)

theorem weightTwoWord_mem_iff {n : ℕ} (P : Pairing n) (u v : Fin n) (huv : u ≠ v) :
    weightTwoWord u v ∈ equalityCode P ↔ pairingMate P u = v := by
  rw [mem_equalityCode_iff_mate]
  constructor
  · intro h
    have h' := h u
    simpa [weightTwoWord, pairingMate_ne] using h'
  · intro h k
    have hv : pairingMate P v = u := by rw [← h, pairingMate_pairingMate]
    have hku : pairingMate P k = u ↔ k = v := by
      constructor
      · intro hk
        have := congrArg (pairingMate P) hk
        simpa [h] using this
      · rintro rfl
        exact hv
    have hkv : pairingMate P k = v ↔ k = u := by
      constructor
      · intro hk
        have := congrArg (pairingMate P) hk
        simpa [hv] using this
      · rintro rfl
        exact h
    simp only [weightTwoWord, hku, hkv, or_comm]

theorem supported_weightTwo_unique_partner {n : ℕ} (P : Pairing n)
    (u v w : Fin n) (huv : u ≠ v) (huw : u ≠ w)
    (hv : weightTwoWord u v ∈ equalityCode P)
    (hw : weightTwoWord u w ∈ equalityCode P) : v = w := by
  exact ((weightTwoWord_mem_iff P u v huv).mp hv).symm.trans
    ((weightTwoWord_mem_iff P u w huw).mp hw)

/-- An equality matching code on at least three ports cannot contain the
weight-two indicator of every pair of distinct ports. -/
theorem not_all_weightTwo_supported {n : ℕ} (P : Pairing n) (hn : 3 ≤ n) :
    ¬ ∀ u v : Fin n, u ≠ v → weightTwoWord u v ∈ equalityCode P := by
  intro h
  let u : Fin n := ⟨0, by omega⟩
  let v : Fin n := ⟨1, by omega⟩
  let w : Fin n := ⟨2, by omega⟩
  have huv : u ≠ v := by intro he; have := congrArg Fin.val he; simp [u, v] at this
  have huw : u ≠ w := by intro he; have := congrArg Fin.val he; simp [u, w] at this
  have hvw := supported_weightTwo_unique_partner P u v w huv huw (h u v huv) (h u w huw)
  have := congrArg Fin.val hvw
  simp [v, w] at this

end
end Paper2.HeightOne.Cyclic
