import Paper2.Complexity.BellMachines.RawTripleGuarded

/-! Real graph invariants under guarded Bell occurrence reduction. Repeated
no-op rounds are harmless; the bounds hold for every requested number of rounds. -/
namespace Paper2.BellReduction
open Complexity ExactInput Problem RawOccurrence BellMachines.RawTriple

theorem guarded_small (G : RawClosedNetwork) (coreLabel : ℕ)
    (hc : markedCount G.vertices ≤ 2) : guarded coreLabel G = G := by
  simp [guarded,hasThree,show ¬ 3 ≤ markedCount G.vertices by omega]

theorem guarded_stats {G : RawClosedNetwork} {s : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s 1 arity) (hzero : arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < s) (ha : arity coreLabel = 8) :
    (guarded coreLabel G).vertices.length ≤ G.vertices.length ∧
    (guarded coreLabel G).edges.length ≤ G.edges.length+2 ∧
    (markedCount (guarded coreLabel G).vertices ≤ 2 ∨
      markedCount (guarded coreLabel G).vertices+1 ≤ markedCount G.vertices) := by
  by_cases hc : 3 ≤ markedCount G.vertices
  · have hs := RawTripleBridge.splitThree_machine hG hzero hc
    have hz : coreLabel ≠ 0 := by intro h; subst coreLabel; omega
    have hV := perform_vertices G coreLabel _ hs
    have hE := perform_edges G coreLabel (BellMachines.RawTriple.split G)
    have hC := perform_count G coreLabel _ hz hs
    have hg : guarded coreLabel G = perform G coreLabel (BellMachines.RawTriple.split G) := by
      simp [guarded,hasThree,hc,transform]
    rw [hg]
    exact ⟨by omega,by omega,Or.inr (by omega)⟩
  · rw [guarded_small G coreLabel (by omega)]
    exact ⟨le_rfl,by omega,Or.inl (by omega)⟩

/-- Every intermediate graph is valid and its actual size grows only linearly;
once at most two marked occurrences remain, no further round changes it. -/
theorem iterate_stats {G : RawClosedNetwork} {s : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s 1 arity) (hzero : arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < s) (ha : arity coreLabel = 8) (k : ℕ) :
    ((guarded coreLabel)^[k] G).WellFormed s 1 arity ∧
    ((guarded coreLabel)^[k] G).vertices.length ≤ G.vertices.length ∧
    ((guarded coreLabel)^[k] G).edges.length ≤ G.edges.length+2*k ∧
    (markedCount ((guarded coreLabel)^[k] G).vertices ≤ 2 ∨
      markedCount ((guarded coreLabel)^[k] G).vertices+k ≤ markedCount G.vertices) := by
  induction k with
  | zero => exact ⟨hG,le_rfl,by simp,Or.inr (by simp)⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hw := guarded_wellFormed ih.1 hzero coreLabel hl ha
    have hs := guarded_stats ih.1 hzero coreLabel hl ha
    refine ⟨hw,le_trans hs.1 ih.2.1,?_,?_⟩
    · have he := ih.2.2.1
      omega
    · rcases ih.2.2.2 with hsmall | hbig
      · rw [guarded_small _ coreLabel hsmall]
        exact Or.inl hsmall
      · rcases hs.2.2 with hsmall | hstep
        · exact Or.inl hsmall
        · exact Or.inr (by omega)

/-- A number of rounds bounded by the original vertex count always suffices. -/
theorem iterate_at_most_two {G : RawClosedNetwork} {s : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s 1 arity) (hzero : arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < s) (ha : arity coreLabel = 8) :
    markedCount ((guarded coreLabel)^[G.vertices.length] G).vertices ≤ 2 := by
  have hi := (iterate_stats hG hzero coreLabel hl ha G.vertices.length).2.2.2
  have hc : markedCount G.vertices ≤ G.vertices.length := List.length_filter_le _ _
  rcases hi with h | h
  · exact h
  · omega

/-- Subtype validation changes no raw transition or byte. -/
theorem guardedValid_iterate_raw (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8)
    (G : Instance L) (k : ℕ) :
    (((guardedValid L hzero coreLabel hl ha)^[k]) G).val = (guarded coreLabel)^[k] G.val := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply',guardedValid,ih]

end Paper2.BellReduction
