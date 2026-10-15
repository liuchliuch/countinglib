import Paper2.Signature
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases

namespace Paper2.Certificates.Q8.Atlas
abbrev Port := Fin 8
abbrev PairIndex := Fin 28
abbrev Choice := Fin 15

def standardMate : Choice → Fin 6 → Fin 6 :=
  ![![1, 0, 3, 2, 5, 4], ![1, 0, 4, 5, 2, 3], ![1, 0, 5, 4, 3, 2], ![2, 3, 0, 1, 5, 4], ![2, 4, 0, 5, 1, 3], ![2, 5, 0, 4, 3, 1], ![3, 2, 1, 0, 5, 4], ![3, 4, 5, 0, 1, 2], ![3, 5, 4, 0, 2, 1], ![4, 2, 1, 5, 0, 3], ![4, 3, 5, 1, 0, 2], ![4, 5, 3, 2, 0, 1], ![5, 2, 1, 4, 3, 0], ![5, 3, 4, 1, 2, 0], ![5, 4, 3, 2, 1, 0]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem standardMate_valid (k : Choice) :
    Function.Involutive (standardMate k) ∧ ∀ i, standardMate k i ≠ i := by
  unfold Function.Involutive
  revert k
  decide +kernel

theorem standardMate_complete (m : Fin 6 → Fin 6)
    (hi : Function.Involutive m) (hn : ∀ i, m i ≠ i) :
    ∃ k : Choice, m = standardMate k := by
  generalize h0 : m 0 = v0
  fin_cases v0
  ·
    change m 0 = 0 at h0
    exact False.elim ((hn 0) h0)
  ·
    change m 0 = 1 at h0
    have h1 : m 1 = 0 := by
      have hh := hi 0
      simpa only [h0] using hh
    generalize h2 : m 2 = v2
    fin_cases v2
    ·
      change m 2 = 0 at h2
      have hc := hi 2
      rw [h2, h0] at hc
      exact False.elim ((by decide : (1 : Fin 6) ≠ 2) hc)
    ·
      change m 2 = 1 at h2
      have hc := hi 2
      rw [h2, h1] at hc
      exact False.elim ((by decide : (0 : Fin 6) ≠ 2) hc)
    ·
      change m 2 = 2 at h2
      exact False.elim ((hn 2) h2)
    ·
      change m 2 = 3 at h2
      have h3 : m 3 = 2 := by
        have hh := hi 2
        simpa only [h2] using hh
      generalize h4 : m 4 = v4
      fin_cases v4
      ·
        change m 4 = 0 at h4
        have hc := hi 4
        rw [h4, h0] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 4) hc)
      ·
        change m 4 = 1 at h4
        have hc := hi 4
        rw [h4, h1] at hc
        exact False.elim ((by decide : (0 : Fin 6) ≠ 4) hc)
      ·
        change m 4 = 2 at h4
        have hc := hi 4
        rw [h4, h2] at hc
        exact False.elim ((by decide : (3 : Fin 6) ≠ 4) hc)
      ·
        change m 4 = 3 at h4
        have hc := hi 4
        rw [h4, h3] at hc
        exact False.elim ((by decide : (2 : Fin 6) ≠ 4) hc)
      ·
        change m 4 = 4 at h4
        exact False.elim ((hn 4) h4)
      ·
        change m 4 = 5 at h4
        have h5 : m 5 = 4 := by
          have hh := hi 4
          simpa only [h4] using hh
        refine ⟨0, ?_⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    ·
      change m 2 = 4 at h2
      have h4 : m 4 = 2 := by
        have hh := hi 2
        simpa only [h2] using hh
      generalize h3 : m 3 = v3
      fin_cases v3
      ·
        change m 3 = 0 at h3
        have hc := hi 3
        rw [h3, h0] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 1 at h3
        have hc := hi 3
        rw [h3, h1] at hc
        exact False.elim ((by decide : (0 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 2 at h3
        have hc := hi 3
        rw [h3, h2] at hc
        exact False.elim ((by decide : (4 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 3 at h3
        exact False.elim ((hn 3) h3)
      ·
        change m 3 = 4 at h3
        have hc := hi 3
        rw [h3, h4] at hc
        exact False.elim ((by decide : (2 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 5 at h3
        have h5 : m 5 = 3 := by
          have hh := hi 3
          simpa only [h3] using hh
        refine ⟨1, ?_⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    ·
      change m 2 = 5 at h2
      have h5 : m 5 = 2 := by
        have hh := hi 2
        simpa only [h2] using hh
      generalize h3 : m 3 = v3
      fin_cases v3
      ·
        change m 3 = 0 at h3
        have hc := hi 3
        rw [h3, h0] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 1 at h3
        have hc := hi 3
        rw [h3, h1] at hc
        exact False.elim ((by decide : (0 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 2 at h3
        have hc := hi 3
        rw [h3, h2] at hc
        exact False.elim ((by decide : (5 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 3 at h3
        exact False.elim ((hn 3) h3)
      ·
        change m 3 = 4 at h3
        have h4 : m 4 = 3 := by
          have hh := hi 3
          simpa only [h3] using hh
        refine ⟨2, ?_⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
      ·
        change m 3 = 5 at h3
        have hc := hi 3
        rw [h3, h5] at hc
        exact False.elim ((by decide : (2 : Fin 6) ≠ 3) hc)
  ·
    change m 0 = 2 at h0
    have h2 : m 2 = 0 := by
      have hh := hi 0
      simpa only [h0] using hh
    generalize h1 : m 1 = v1
    fin_cases v1
    ·
      change m 1 = 0 at h1
      have hc := hi 1
      rw [h1, h0] at hc
      exact False.elim ((by decide : (2 : Fin 6) ≠ 1) hc)
    ·
      change m 1 = 1 at h1
      exact False.elim ((hn 1) h1)
    ·
      change m 1 = 2 at h1
      have hc := hi 1
      rw [h1, h2] at hc
      exact False.elim ((by decide : (0 : Fin 6) ≠ 1) hc)
    ·
      change m 1 = 3 at h1
      have h3 : m 3 = 1 := by
        have hh := hi 1
        simpa only [h1] using hh
      generalize h4 : m 4 = v4
      fin_cases v4
      ·
        change m 4 = 0 at h4
        have hc := hi 4
        rw [h4, h0] at hc
        exact False.elim ((by decide : (2 : Fin 6) ≠ 4) hc)
      ·
        change m 4 = 1 at h4
        have hc := hi 4
        rw [h4, h1] at hc
        exact False.elim ((by decide : (3 : Fin 6) ≠ 4) hc)
      ·
        change m 4 = 2 at h4
        have hc := hi 4
        rw [h4, h2] at hc
        exact False.elim ((by decide : (0 : Fin 6) ≠ 4) hc)
      ·
        change m 4 = 3 at h4
        have hc := hi 4
        rw [h4, h3] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 4) hc)
      ·
        change m 4 = 4 at h4
        exact False.elim ((hn 4) h4)
      ·
        change m 4 = 5 at h4
        have h5 : m 5 = 4 := by
          have hh := hi 4
          simpa only [h4] using hh
        refine ⟨3, ?_⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    ·
      change m 1 = 4 at h1
      have h4 : m 4 = 1 := by
        have hh := hi 1
        simpa only [h1] using hh
      generalize h3 : m 3 = v3
      fin_cases v3
      ·
        change m 3 = 0 at h3
        have hc := hi 3
        rw [h3, h0] at hc
        exact False.elim ((by decide : (2 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 1 at h3
        have hc := hi 3
        rw [h3, h1] at hc
        exact False.elim ((by decide : (4 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 2 at h3
        have hc := hi 3
        rw [h3, h2] at hc
        exact False.elim ((by decide : (0 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 3 at h3
        exact False.elim ((hn 3) h3)
      ·
        change m 3 = 4 at h3
        have hc := hi 3
        rw [h3, h4] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 5 at h3
        have h5 : m 5 = 3 := by
          have hh := hi 3
          simpa only [h3] using hh
        refine ⟨4, ?_⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    ·
      change m 1 = 5 at h1
      have h5 : m 5 = 1 := by
        have hh := hi 1
        simpa only [h1] using hh
      generalize h3 : m 3 = v3
      fin_cases v3
      ·
        change m 3 = 0 at h3
        have hc := hi 3
        rw [h3, h0] at hc
        exact False.elim ((by decide : (2 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 1 at h3
        have hc := hi 3
        rw [h3, h1] at hc
        exact False.elim ((by decide : (5 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 2 at h3
        have hc := hi 3
        rw [h3, h2] at hc
        exact False.elim ((by decide : (0 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 3 at h3
        exact False.elim ((hn 3) h3)
      ·
        change m 3 = 4 at h3
        have h4 : m 4 = 3 := by
          have hh := hi 3
          simpa only [h3] using hh
        refine ⟨5, ?_⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
      ·
        change m 3 = 5 at h3
        have hc := hi 3
        rw [h3, h5] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 3) hc)
  ·
    change m 0 = 3 at h0
    have h3 : m 3 = 0 := by
      have hh := hi 0
      simpa only [h0] using hh
    generalize h1 : m 1 = v1
    fin_cases v1
    ·
      change m 1 = 0 at h1
      have hc := hi 1
      rw [h1, h0] at hc
      exact False.elim ((by decide : (3 : Fin 6) ≠ 1) hc)
    ·
      change m 1 = 1 at h1
      exact False.elim ((hn 1) h1)
    ·
      change m 1 = 2 at h1
      have h2 : m 2 = 1 := by
        have hh := hi 1
        simpa only [h1] using hh
      generalize h4 : m 4 = v4
      fin_cases v4
      ·
        change m 4 = 0 at h4
        have hc := hi 4
        rw [h4, h0] at hc
        exact False.elim ((by decide : (3 : Fin 6) ≠ 4) hc)
      ·
        change m 4 = 1 at h4
        have hc := hi 4
        rw [h4, h1] at hc
        exact False.elim ((by decide : (2 : Fin 6) ≠ 4) hc)
      ·
        change m 4 = 2 at h4
        have hc := hi 4
        rw [h4, h2] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 4) hc)
      ·
        change m 4 = 3 at h4
        have hc := hi 4
        rw [h4, h3] at hc
        exact False.elim ((by decide : (0 : Fin 6) ≠ 4) hc)
      ·
        change m 4 = 4 at h4
        exact False.elim ((hn 4) h4)
      ·
        change m 4 = 5 at h4
        have h5 : m 5 = 4 := by
          have hh := hi 4
          simpa only [h4] using hh
        refine ⟨6, ?_⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    ·
      change m 1 = 3 at h1
      have hc := hi 1
      rw [h1, h3] at hc
      exact False.elim ((by decide : (0 : Fin 6) ≠ 1) hc)
    ·
      change m 1 = 4 at h1
      have h4 : m 4 = 1 := by
        have hh := hi 1
        simpa only [h1] using hh
      generalize h2 : m 2 = v2
      fin_cases v2
      ·
        change m 2 = 0 at h2
        have hc := hi 2
        rw [h2, h0] at hc
        exact False.elim ((by decide : (3 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 1 at h2
        have hc := hi 2
        rw [h2, h1] at hc
        exact False.elim ((by decide : (4 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 2 at h2
        exact False.elim ((hn 2) h2)
      ·
        change m 2 = 3 at h2
        have hc := hi 2
        rw [h2, h3] at hc
        exact False.elim ((by decide : (0 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 4 at h2
        have hc := hi 2
        rw [h2, h4] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 5 at h2
        have h5 : m 5 = 2 := by
          have hh := hi 2
          simpa only [h2] using hh
        refine ⟨7, ?_⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    ·
      change m 1 = 5 at h1
      have h5 : m 5 = 1 := by
        have hh := hi 1
        simpa only [h1] using hh
      generalize h2 : m 2 = v2
      fin_cases v2
      ·
        change m 2 = 0 at h2
        have hc := hi 2
        rw [h2, h0] at hc
        exact False.elim ((by decide : (3 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 1 at h2
        have hc := hi 2
        rw [h2, h1] at hc
        exact False.elim ((by decide : (5 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 2 at h2
        exact False.elim ((hn 2) h2)
      ·
        change m 2 = 3 at h2
        have hc := hi 2
        rw [h2, h3] at hc
        exact False.elim ((by decide : (0 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 4 at h2
        have h4 : m 4 = 2 := by
          have hh := hi 2
          simpa only [h2] using hh
        refine ⟨8, ?_⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
      ·
        change m 2 = 5 at h2
        have hc := hi 2
        rw [h2, h5] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 2) hc)
  ·
    change m 0 = 4 at h0
    have h4 : m 4 = 0 := by
      have hh := hi 0
      simpa only [h0] using hh
    generalize h1 : m 1 = v1
    fin_cases v1
    ·
      change m 1 = 0 at h1
      have hc := hi 1
      rw [h1, h0] at hc
      exact False.elim ((by decide : (4 : Fin 6) ≠ 1) hc)
    ·
      change m 1 = 1 at h1
      exact False.elim ((hn 1) h1)
    ·
      change m 1 = 2 at h1
      have h2 : m 2 = 1 := by
        have hh := hi 1
        simpa only [h1] using hh
      generalize h3 : m 3 = v3
      fin_cases v3
      ·
        change m 3 = 0 at h3
        have hc := hi 3
        rw [h3, h0] at hc
        exact False.elim ((by decide : (4 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 1 at h3
        have hc := hi 3
        rw [h3, h1] at hc
        exact False.elim ((by decide : (2 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 2 at h3
        have hc := hi 3
        rw [h3, h2] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 3 at h3
        exact False.elim ((hn 3) h3)
      ·
        change m 3 = 4 at h3
        have hc := hi 3
        rw [h3, h4] at hc
        exact False.elim ((by decide : (0 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 5 at h3
        have h5 : m 5 = 3 := by
          have hh := hi 3
          simpa only [h3] using hh
        refine ⟨9, ?_⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    ·
      change m 1 = 3 at h1
      have h3 : m 3 = 1 := by
        have hh := hi 1
        simpa only [h1] using hh
      generalize h2 : m 2 = v2
      fin_cases v2
      ·
        change m 2 = 0 at h2
        have hc := hi 2
        rw [h2, h0] at hc
        exact False.elim ((by decide : (4 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 1 at h2
        have hc := hi 2
        rw [h2, h1] at hc
        exact False.elim ((by decide : (3 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 2 at h2
        exact False.elim ((hn 2) h2)
      ·
        change m 2 = 3 at h2
        have hc := hi 2
        rw [h2, h3] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 4 at h2
        have hc := hi 2
        rw [h2, h4] at hc
        exact False.elim ((by decide : (0 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 5 at h2
        have h5 : m 5 = 2 := by
          have hh := hi 2
          simpa only [h2] using hh
        refine ⟨10, ?_⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
    ·
      change m 1 = 4 at h1
      have hc := hi 1
      rw [h1, h4] at hc
      exact False.elim ((by decide : (0 : Fin 6) ≠ 1) hc)
    ·
      change m 1 = 5 at h1
      have h5 : m 5 = 1 := by
        have hh := hi 1
        simpa only [h1] using hh
      generalize h2 : m 2 = v2
      fin_cases v2
      ·
        change m 2 = 0 at h2
        have hc := hi 2
        rw [h2, h0] at hc
        exact False.elim ((by decide : (4 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 1 at h2
        have hc := hi 2
        rw [h2, h1] at hc
        exact False.elim ((by decide : (5 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 2 at h2
        exact False.elim ((hn 2) h2)
      ·
        change m 2 = 3 at h2
        have h3 : m 3 = 2 := by
          have hh := hi 2
          simpa only [h2] using hh
        refine ⟨11, ?_⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
      ·
        change m 2 = 4 at h2
        have hc := hi 2
        rw [h2, h4] at hc
        exact False.elim ((by decide : (0 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 5 at h2
        have hc := hi 2
        rw [h2, h5] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 2) hc)
  ·
    change m 0 = 5 at h0
    have h5 : m 5 = 0 := by
      have hh := hi 0
      simpa only [h0] using hh
    generalize h1 : m 1 = v1
    fin_cases v1
    ·
      change m 1 = 0 at h1
      have hc := hi 1
      rw [h1, h0] at hc
      exact False.elim ((by decide : (5 : Fin 6) ≠ 1) hc)
    ·
      change m 1 = 1 at h1
      exact False.elim ((hn 1) h1)
    ·
      change m 1 = 2 at h1
      have h2 : m 2 = 1 := by
        have hh := hi 1
        simpa only [h1] using hh
      generalize h3 : m 3 = v3
      fin_cases v3
      ·
        change m 3 = 0 at h3
        have hc := hi 3
        rw [h3, h0] at hc
        exact False.elim ((by decide : (5 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 1 at h3
        have hc := hi 3
        rw [h3, h1] at hc
        exact False.elim ((by decide : (2 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 2 at h3
        have hc := hi 3
        rw [h3, h2] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 3) hc)
      ·
        change m 3 = 3 at h3
        exact False.elim ((hn 3) h3)
      ·
        change m 3 = 4 at h3
        have h4 : m 4 = 3 := by
          have hh := hi 3
          simpa only [h3] using hh
        refine ⟨12, ?_⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
      ·
        change m 3 = 5 at h3
        have hc := hi 3
        rw [h3, h5] at hc
        exact False.elim ((by decide : (0 : Fin 6) ≠ 3) hc)
    ·
      change m 1 = 3 at h1
      have h3 : m 3 = 1 := by
        have hh := hi 1
        simpa only [h1] using hh
      generalize h2 : m 2 = v2
      fin_cases v2
      ·
        change m 2 = 0 at h2
        have hc := hi 2
        rw [h2, h0] at hc
        exact False.elim ((by decide : (5 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 1 at h2
        have hc := hi 2
        rw [h2, h1] at hc
        exact False.elim ((by decide : (3 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 2 at h2
        exact False.elim ((hn 2) h2)
      ·
        change m 2 = 3 at h2
        have hc := hi 2
        rw [h2, h3] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 4 at h2
        have h4 : m 4 = 2 := by
          have hh := hi 2
          simpa only [h2] using hh
        refine ⟨13, ?_⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
      ·
        change m 2 = 5 at h2
        have hc := hi 2
        rw [h2, h5] at hc
        exact False.elim ((by decide : (0 : Fin 6) ≠ 2) hc)
    ·
      change m 1 = 4 at h1
      have h4 : m 4 = 1 := by
        have hh := hi 1
        simpa only [h1] using hh
      generalize h2 : m 2 = v2
      fin_cases v2
      ·
        change m 2 = 0 at h2
        have hc := hi 2
        rw [h2, h0] at hc
        exact False.elim ((by decide : (5 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 1 at h2
        have hc := hi 2
        rw [h2, h1] at hc
        exact False.elim ((by decide : (4 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 2 at h2
        exact False.elim ((hn 2) h2)
      ·
        change m 2 = 3 at h2
        have h3 : m 3 = 2 := by
          have hh := hi 2
          simpa only [h2] using hh
        refine ⟨14, ?_⟩
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
        · exact h5
      ·
        change m 2 = 4 at h2
        have hc := hi 2
        rw [h2, h4] at hc
        exact False.elim ((by decide : (1 : Fin 6) ≠ 2) hc)
      ·
        change m 2 = 5 at h2
        have hc := hi 2
        rw [h2, h5] at hc
        exact False.elim ((by decide : (0 : Fin 6) ≠ 2) hc)
    ·
      change m 1 = 5 at h1
      have hc := hi 1
      rw [h1, h5] at hc
      exact False.elim ((by decide : (0 : Fin 6) ≠ 1) hc)

end Paper2.Certificates.Q8.Atlas
