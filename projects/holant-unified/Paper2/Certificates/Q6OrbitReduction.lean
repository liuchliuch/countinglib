import Paper2.Certificates.Q6SparseCards
import Paper2.Certificates.Q6SparseLoops
import Paper2.Certificates.Q6SparseBlocks
import Paper2.Certificates.Q6DenseReduction

/-! Exact algebraic elimination for every official signed row. The hypotheses
are the actual loop arrays and actual two-copy subset-sum cards, not a solver
transcript or an asserted finite-classification result. -/
namespace Paper2.Certificates.Q6
variable {K : Type*} [CommRing K] [NoZeroDivisors K] [CharZero K]

private theorem reduce_orbit_0 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 0))
    (hc : AllTwoCopySafe (fullOrbit u 0) t) : OneComplementPair (fullOrbit u 0) := by
  refine ⟨0, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl)

private theorem reduce_orbit_1 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 1))
    (hc : AllTwoCopySafe (fullOrbit u 1) t) : OneComplementPair (fullOrbit u 1) := by
  refine ⟨9, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl)

private theorem reduce_orbit_2 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 2))
    (hc : AllTwoCopySafe (fullOrbit u 2) t) : OneComplementPair (fullOrbit u 2) := by
  have hz := square_product_card_zero t (u 0) (u 1) 1 (-1) ht (by norm_num) (by norm_num)
    (by simpa only [one_mul, neg_one_mul] using
      (show NecessarySafe ![t,(u 1)^2,-u 0*u 1,-u 0*u 1,(u 0)^2,t] from sparse_formula_safe u t 0 hc))
  refine ⟨0, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl) |
    exact False.elim (hj hz.1) |
    exact False.elim (hj (neg_eq_zero.mpr hz.1)) |
    exact False.elim (hj hz.2) |
    exact False.elim (hj (neg_eq_zero.mpr hz.2))

private theorem reduce_orbit_3 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 3))
    (hc : AllTwoCopySafe (fullOrbit u 3) t) : OneComplementPair (fullOrbit u 3) := by
  have hz := sparse3_one_pair t (u 0) (u 1) (u 2) (u 3) ht
    (by simpa only [zero_add, add_zero, neg_add_cancel, add_neg_cancel] using selected_loop_3_0 u hl) (sparse_formula_safe u t 1 hc)
  rcases hz with hz | hz
  ·
    refine ⟨9, ?_⟩
    intro j hj
    fin_cases j
    all_goals first | exact Or.inl rfl |
      exact Or.inr rfl |
      exact False.elim (hj rfl) |
      exact False.elim (hj hz.1) |
      exact False.elim (hj (neg_eq_zero.mpr hz.1)) |
      exact False.elim (hj hz.2) |
      exact False.elim (hj (neg_eq_zero.mpr hz.2))

  ·
    refine ⟨8, ?_⟩
    intro j hj
    fin_cases j
    all_goals first | exact Or.inl rfl |
      exact Or.inr rfl |
      exact False.elim (hj rfl) |
      exact False.elim (hj hz.1) |
      exact False.elim (hj (neg_eq_zero.mpr hz.1)) |
      exact False.elim (hj hz.2) |
      exact False.elim (hj (neg_eq_zero.mpr hz.2))

private theorem reduce_orbit_4 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 4))
    (hc : AllTwoCopySafe (fullOrbit u 4) t) : OneComplementPair (fullOrbit u 4) := by
  have hz := sparse4_zero t (u 0) ht (sparse_formula_safe u t 2 hc)
  refine ⟨0, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl) |
    exact False.elim (hj hz) |
    exact False.elim (hj (neg_eq_zero.mpr hz))

private theorem reduce_orbit_5 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 5))
    (hc : AllTwoCopySafe (fullOrbit u 5) t) : OneComplementPair (fullOrbit u 5) := by
  have hz := square_product_card_zero t (u 0) (u 1) 2 (-3) ht (by norm_num) (by norm_num) (sparse_formula_safe u t 3 hc)
  refine ⟨0, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl) |
    exact False.elim (hj hz.1) |
    exact False.elim (hj (neg_eq_zero.mpr hz.1)) |
    exact False.elim (hj hz.2) |
    exact False.elim (hj (neg_eq_zero.mpr hz.2))

private theorem reduce_orbit_6 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 6))
    (hc : AllTwoCopySafe (fullOrbit u 6) t) : OneComplementPair (fullOrbit u 6) := by
  have hz := square_square_card_zero t (u 1) (u 2) (-1) 1 ht (by norm_num) (by norm_num)
    (by simpa only [one_mul, neg_one_mul] using
      (show NecessarySafe ![t,-(u 2)^2,(u 2)^2,(u 1)^2,-(u 1)^2,t] from sparse_formula_safe u t 4 hc))
  refine ⟨6, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl) |
    exact False.elim (hj hz.1) |
    exact False.elim (hj (neg_eq_zero.mpr hz.1)) |
    exact False.elim (hj hz.2) |
    exact False.elim (hj (neg_eq_zero.mpr hz.2))

private theorem reduce_orbit_7 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 7))
    (hc : AllTwoCopySafe (fullOrbit u 7) t) : OneComplementPair (fullOrbit u 7) := by
  have hb := sparse7_one_block t (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) ht
    (by simpa only [zero_add, add_zero, neg_add_cancel, add_neg_cancel] using selected_loop_7_1 u hl) (by simpa only [zero_add, add_zero, neg_add_cancel, add_neg_cancel] using selected_loop_7_2 u hl)
    (sparse_formula_safe u t 5 hc) (sparse_formula_safe u t 6 hc) (sparse_formula_safe u t 7 hc)
  obtain ⟨i, hi⟩ := hb
  fin_cases i
  ·
    have h1 : u 1 = 0 := (hi 1 (by decide)).1
    have h4 : u 4 = 0 := (hi 1 (by decide)).2
    have h2 : u 2 = 0 := (hi 2 (by decide)).1
    have h3 : u 3 = 0 := (hi 2 (by decide)).2
    refine ⟨6, ?_⟩
    intro j hj
    fin_cases j
    all_goals first | exact Or.inl rfl |
      exact Or.inr rfl |
      exact False.elim (hj rfl) |
      exact False.elim (hj h1) |
      exact False.elim (hj (neg_eq_zero.mpr h1)) |
      exact False.elim (hj h4) |
      exact False.elim (hj (neg_eq_zero.mpr h4)) |
      exact False.elim (hj h2) |
      exact False.elim (hj (neg_eq_zero.mpr h2)) |
      exact False.elim (hj h3) |
      exact False.elim (hj (neg_eq_zero.mpr h3))

  ·
    have h0 : u 0 = 0 := (hi 0 (by decide)).1
    have h5 : u 5 = 0 := (hi 0 (by decide)).2
    have h2 : u 2 = 0 := (hi 2 (by decide)).1
    have h3 : u 3 = 0 := (hi 2 (by decide)).2
    refine ⟨7, ?_⟩
    intro j hj
    fin_cases j
    all_goals first | exact Or.inl rfl |
      exact Or.inr rfl |
      exact False.elim (hj rfl) |
      exact False.elim (hj h0) |
      exact False.elim (hj (neg_eq_zero.mpr h0)) |
      exact False.elim (hj h5) |
      exact False.elim (hj (neg_eq_zero.mpr h5)) |
      exact False.elim (hj h2) |
      exact False.elim (hj (neg_eq_zero.mpr h2)) |
      exact False.elim (hj h3) |
      exact False.elim (hj (neg_eq_zero.mpr h3))

  ·
    have h0 : u 0 = 0 := (hi 0 (by decide)).1
    have h5 : u 5 = 0 := (hi 0 (by decide)).2
    have h1 : u 1 = 0 := (hi 1 (by decide)).1
    have h4 : u 4 = 0 := (hi 1 (by decide)).2
    refine ⟨9, ?_⟩
    intro j hj
    fin_cases j
    all_goals first | exact Or.inl rfl |
      exact Or.inr rfl |
      exact False.elim (hj rfl) |
      exact False.elim (hj h0) |
      exact False.elim (hj (neg_eq_zero.mpr h0)) |
      exact False.elim (hj h5) |
      exact False.elim (hj (neg_eq_zero.mpr h5)) |
      exact False.elim (hj h1) |
      exact False.elim (hj (neg_eq_zero.mpr h1)) |
      exact False.elim (hj h4) |
      exact False.elim (hj (neg_eq_zero.mpr h4))

private theorem reduce_orbit_8 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 8))
    (hc : AllTwoCopySafe (fullOrbit u 8) t) : OneComplementPair (fullOrbit u 8) := by
  have hz := sparse8_one_pair t (u 0) (u 3) ht (sparse_formula_safe u t 8 hc)
  refine ⟨8, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl) |
    exact False.elim (hj hz.1) |
    exact False.elim (hj (neg_eq_zero.mpr hz.1)) |
    exact False.elim (hj hz.2) |
    exact False.elim (hj (neg_eq_zero.mpr hz.2))

private theorem reduce_orbit_9 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 9))
    (hc : AllTwoCopySafe (fullOrbit u 9) t) : OneComplementPair (fullOrbit u 9) := by
  have hz := sparse9_one_block t (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) ht
    (by simpa only [zero_add, add_zero, neg_add_cancel, add_neg_cancel] using selected_loop_9_1 u hl) (sparse_formula_safe u t 9 hc) (sparse_formula_safe u t 10 hc)
  have hb := hz.2.2
  obtain ⟨i, hi⟩ := hb
  fin_cases i
  ·
    have h2 : u 2 = 0 := (hi 1 (by decide)).1
    have h3 : u 3 = 0 := (hi 1 (by decide)).2
    refine ⟨7, ?_⟩
    intro j hj
    fin_cases j
    all_goals first | exact Or.inl rfl |
      exact Or.inr rfl |
      exact False.elim (hj rfl) |
      exact False.elim (hj hz.1) |
      exact False.elim (hj (neg_eq_zero.mpr hz.1)) |
      exact False.elim (hj hz.2.1) |
      exact False.elim (hj (neg_eq_zero.mpr hz.2.1)) |
      exact False.elim (hj h2) |
      exact False.elim (hj (neg_eq_zero.mpr h2)) |
      exact False.elim (hj h3) |
      exact False.elim (hj (neg_eq_zero.mpr h3))

  ·
    have h1 : u 1 = 0 := (hi 0 (by decide)).1
    have h4 : u 4 = 0 := (hi 0 (by decide)).2
    refine ⟨8, ?_⟩
    intro j hj
    fin_cases j
    all_goals first | exact Or.inl rfl |
      exact Or.inr rfl |
      exact False.elim (hj rfl) |
      exact False.elim (hj hz.1) |
      exact False.elim (hj (neg_eq_zero.mpr hz.1)) |
      exact False.elim (hj hz.2.1) |
      exact False.elim (hj (neg_eq_zero.mpr hz.2.1)) |
      exact False.elim (hj h1) |
      exact False.elim (hj (neg_eq_zero.mpr h1)) |
      exact False.elim (hj h4) |
      exact False.elim (hj (neg_eq_zero.mpr h4))

private theorem reduce_orbit_10 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 10))
    (hc : AllTwoCopySafe (fullOrbit u 10) t) : OneComplementPair (fullOrbit u 10) := by
  have hb := sparse10_one_block t (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) (u 6) (u 7) ht
    (by simpa only [zero_add, add_zero, neg_add_cancel, add_neg_cancel] using selected_loop_10_1 u hl) (by simpa only [zero_add, add_zero, neg_add_cancel, add_neg_cancel] using selected_loop_10_2 u hl)
    (sparse_formula_safe u t 11 hc) (sparse_formula_safe u t 12 hc) (sparse_formula_safe u t 13 hc) (sparse_formula_safe u t 14 hc) (sparse_formula_safe u t 15 hc) (sparse_formula_safe u t 16 hc)
  obtain ⟨i, hi⟩ := hb
  fin_cases i
  ·
    have h1 : u 1 = 0 := (hi 1 (by decide)).1
    have h6 : u 6 = 0 := (hi 1 (by decide)).2
    have h2 : u 2 = 0 := (hi 2 (by decide)).1
    have h5 : u 5 = 0 := (hi 2 (by decide)).2
    have h3 : u 3 = 0 := (hi 3 (by decide)).1
    have h4 : u 4 = 0 := (hi 3 (by decide)).2
    refine ⟨5, ?_⟩
    intro j hj
    fin_cases j
    all_goals first | exact Or.inl rfl |
      exact Or.inr rfl |
      exact False.elim (hj rfl) |
      exact False.elim (hj h1) |
      exact False.elim (hj (neg_eq_zero.mpr h1)) |
      exact False.elim (hj h6) |
      exact False.elim (hj (neg_eq_zero.mpr h6)) |
      exact False.elim (hj h2) |
      exact False.elim (hj (neg_eq_zero.mpr h2)) |
      exact False.elim (hj h5) |
      exact False.elim (hj (neg_eq_zero.mpr h5)) |
      exact False.elim (hj h3) |
      exact False.elim (hj (neg_eq_zero.mpr h3)) |
      exact False.elim (hj h4) |
      exact False.elim (hj (neg_eq_zero.mpr h4))

  ·
    have h0 : u 0 = 0 := (hi 0 (by decide)).1
    have h7 : u 7 = 0 := (hi 0 (by decide)).2
    have h2 : u 2 = 0 := (hi 2 (by decide)).1
    have h5 : u 5 = 0 := (hi 2 (by decide)).2
    have h3 : u 3 = 0 := (hi 3 (by decide)).1
    have h4 : u 4 = 0 := (hi 3 (by decide)).2
    refine ⟨6, ?_⟩
    intro j hj
    fin_cases j
    all_goals first | exact Or.inl rfl |
      exact Or.inr rfl |
      exact False.elim (hj rfl) |
      exact False.elim (hj h0) |
      exact False.elim (hj (neg_eq_zero.mpr h0)) |
      exact False.elim (hj h7) |
      exact False.elim (hj (neg_eq_zero.mpr h7)) |
      exact False.elim (hj h2) |
      exact False.elim (hj (neg_eq_zero.mpr h2)) |
      exact False.elim (hj h5) |
      exact False.elim (hj (neg_eq_zero.mpr h5)) |
      exact False.elim (hj h3) |
      exact False.elim (hj (neg_eq_zero.mpr h3)) |
      exact False.elim (hj h4) |
      exact False.elim (hj (neg_eq_zero.mpr h4))

  ·
    have h0 : u 0 = 0 := (hi 0 (by decide)).1
    have h7 : u 7 = 0 := (hi 0 (by decide)).2
    have h1 : u 1 = 0 := (hi 1 (by decide)).1
    have h6 : u 6 = 0 := (hi 1 (by decide)).2
    have h3 : u 3 = 0 := (hi 3 (by decide)).1
    have h4 : u 4 = 0 := (hi 3 (by decide)).2
    refine ⟨7, ?_⟩
    intro j hj
    fin_cases j
    all_goals first | exact Or.inl rfl |
      exact Or.inr rfl |
      exact False.elim (hj rfl) |
      exact False.elim (hj h0) |
      exact False.elim (hj (neg_eq_zero.mpr h0)) |
      exact False.elim (hj h7) |
      exact False.elim (hj (neg_eq_zero.mpr h7)) |
      exact False.elim (hj h1) |
      exact False.elim (hj (neg_eq_zero.mpr h1)) |
      exact False.elim (hj h6) |
      exact False.elim (hj (neg_eq_zero.mpr h6)) |
      exact False.elim (hj h3) |
      exact False.elim (hj (neg_eq_zero.mpr h3)) |
      exact False.elim (hj h4) |
      exact False.elim (hj (neg_eq_zero.mpr h4))

  ·
    have h0 : u 0 = 0 := (hi 0 (by decide)).1
    have h7 : u 7 = 0 := (hi 0 (by decide)).2
    have h1 : u 1 = 0 := (hi 1 (by decide)).1
    have h6 : u 6 = 0 := (hi 1 (by decide)).2
    have h2 : u 2 = 0 := (hi 2 (by decide)).1
    have h5 : u 5 = 0 := (hi 2 (by decide)).2
    refine ⟨8, ?_⟩
    intro j hj
    fin_cases j
    all_goals first | exact Or.inl rfl |
      exact Or.inr rfl |
      exact False.elim (hj rfl) |
      exact False.elim (hj h0) |
      exact False.elim (hj (neg_eq_zero.mpr h0)) |
      exact False.elim (hj h7) |
      exact False.elim (hj (neg_eq_zero.mpr h7)) |
      exact False.elim (hj h1) |
      exact False.elim (hj (neg_eq_zero.mpr h1)) |
      exact False.elim (hj h6) |
      exact False.elim (hj (neg_eq_zero.mpr h6)) |
      exact False.elim (hj h2) |
      exact False.elim (hj (neg_eq_zero.mpr h2)) |
      exact False.elim (hj h5) |
      exact False.elim (hj (neg_eq_zero.mpr h5))

private theorem reduce_orbit_11 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 11))
    (hc : AllTwoCopySafe (fullOrbit u 11) t) : OneComplementPair (fullOrbit u 11) := by
  have hz := unequal_middle_card (-4*(u 0)^2+t) (-2) (-6) (u 0)
    (by norm_num) (by norm_num) (by norm_num) (sparse_formula_safe u t 17 hc)
  refine ⟨0, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl) |
    exact False.elim (hj hz) |
    exact False.elim (hj (neg_eq_zero.mpr hz))

private theorem reduce_orbit_12 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 12))
    (hc : AllTwoCopySafe (fullOrbit u 12) t) : OneComplementPair (fullOrbit u 12) := by
  have hz := unequal_middle_card (4*(u 0)^2+t) (-2) (6) (u 0)
    (by norm_num) (by norm_num) (by norm_num) (sparse_formula_safe u t 18 hc)
  refine ⟨0, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl) |
    exact False.elim (hj hz) |
    exact False.elim (hj (neg_eq_zero.mpr hz))

private theorem reduce_orbit_13 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 13))
    (hc : AllTwoCopySafe (fullOrbit u 13) t) : OneComplementPair (fullOrbit u 13) := by
  have hz := unequal_middle_card (-4*(u 0)^2+t) (2) (-6) (u 0)
    (by norm_num) (by norm_num) (by norm_num) (sparse_formula_safe u t 19 hc)
  refine ⟨0, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl) |
    exact False.elim (hj hz) |
    exact False.elim (hj (neg_eq_zero.mpr hz))

private theorem reduce_orbit_14 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 14))
    (hc : AllTwoCopySafe (fullOrbit u 14) t) : OneComplementPair (fullOrbit u 14) := by
  have hz := unequal_middle_card (-3*(u 0)^2+u 1*u 2+t) (2) (-6) (u 0)
    (by norm_num) (by norm_num) (by norm_num) (sparse_formula_safe u t 20 hc)
  refine ⟨7, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl) |
    exact False.elim (hj hz) |
    exact False.elim (hj (neg_eq_zero.mpr hz))

private theorem reduce_orbit_15 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 15))
    (hc : AllTwoCopySafe (fullOrbit u 15) t) : OneComplementPair (fullOrbit u 15) := by
  have hz := unequal_middle_card (4*(u 0)^2+t) (-2) (6) (u 0)
    (by norm_num) (by norm_num) (by norm_num) (sparse_formula_safe u t 21 hc)
  refine ⟨0, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl) |
    exact False.elim (hj hz) |
    exact False.elim (hj (neg_eq_zero.mpr hz))

private theorem reduce_orbit_17 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 17))
    (hc : AllTwoCopySafe (fullOrbit u 17) t) : OneComplementPair (fullOrbit u 17) := by
  have hz := unequal_middle_card (-4*(u 0)^2+t) (2) (-6) (u 0)
    (by norm_num) (by norm_num) (by norm_num) (sparse_formula_safe u t 24 hc)
  refine ⟨0, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl) |
    exact False.elim (hj hz) |
    exact False.elim (hj (neg_eq_zero.mpr hz))

private theorem reduce_orbit_18 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 18))
    (hc : AllTwoCopySafe (fullOrbit u 18) t) : OneComplementPair (fullOrbit u 18) := by
  have hz := unequal_middle_card (-3*(u 0)^2+u 1*u 2+t) (2) (-6) (u 0)
    (by norm_num) (by norm_num) (by norm_num) (sparse_formula_safe u t 25 hc)
  refine ⟨9, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl) |
    exact False.elim (hj hz) |
    exact False.elim (hj (neg_eq_zero.mpr hz))

private theorem reduce_orbit_16 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 16))
    (hc : AllTwoCopySafe (fullOrbit u 16) t) : OneComplementPair (fullOrbit u 16) := by
  have hz := sparse16_zero t (u 0) (u 1) (u 2) (2*(u 0)^2-2*u 1*u 2+t) ht
    (sparse_formula_safe u t 22 hc) (sparse_formula_safe u t 23 hc)
  refine ⟨0, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl) |
    exact False.elim (hj hz.1) |
    exact False.elim (hj (neg_eq_zero.mpr hz.1)) |
    exact False.elim (hj hz.2.1) |
    exact False.elim (hj (neg_eq_zero.mpr hz.2.1)) |
    exact False.elim (hj hz.2.2) |
    exact False.elim (hj (neg_eq_zero.mpr hz.2.2))

private theorem reduce_orbit_19 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 19))
    (hc : AllTwoCopySafe (fullOrbit u 19) t) : OneComplementPair (fullOrbit u 19) := by
  have hz := sparse19_zero t (u 0) (u 1) (u 2) (-2*(u 0)^2-2*u 1*u 2+t) ht
    (sparse_formula_safe u t 26 hc) (sparse_formula_safe u t 27 hc)
  refine ⟨0, ?_⟩
  intro j hj
  fin_cases j
  all_goals first | exact Or.inl rfl |
    exact Or.inr rfl |
    exact False.elim (hj rfl) |
    exact False.elim (hj hz.1) |
    exact False.elim (hj (neg_eq_zero.mpr hz.1)) |
    exact False.elim (hj hz.2.1) |
    exact False.elim (hj (neg_eq_zero.mpr hz.2.1)) |
    exact False.elim (hj hz.2.2) |
    exact False.elim (hj (neg_eq_zero.mpr hz.2.2))

private theorem reduce_orbit_20 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 20))
    (hc : AllTwoCopySafe (fullOrbit u 20) t) : OneComplementPair (fullOrbit u 20) := by
  have ha : u 0 = 0 := dense20_from_array ![u 0,u 1,u 2,u 3,u 4] t
    (hc (denseSpecs 0) (dense_specs_valid 0))
  have hl0 : NecessarySafe ![0,u 3,u 4,u 1,u 2,0] := by
    simpa only [ha, neg_zero, zero_add, add_zero] using selected_loop_20_0 u hl
  have hc0 : NecessarySafe ![t,(u 4)^2,u 2*u 3,u 2*u 3,(u 1)^2,t] := by
    have h : NecessarySafe ![4*(u 0)^2+t,3*(u 0)^2-2*u 0*u 3+(u 4)^2,
      -3*(u 0)^2+u 0*u 1-u 0*u 4+u 2*u 3,
      -3*(u 0)^2+u 0*u 1-u 0*u 4+u 2*u 3,
      3*(u 0)^2+2*u 0*u 2+(u 1)^2,4*(u 0)^2+t] := sparse_formula_safe u t 28 hc
    simpa only [ha, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, neg_zero,
      sub_zero, zero_sub, add_zero, zero_add] using h
  have hz := two_blocks_card t (u 1) (u 2) (u 3) (u 4) ht hl0 hc0
  rcases hz with hz | hz
  ·
    refine ⟨8, ?_⟩
    intro j hj
    fin_cases j
    all_goals first | exact Or.inl rfl |
      exact Or.inr rfl |
      exact False.elim (hj rfl) |
      exact False.elim (hj ha) |
      exact False.elim (hj (neg_eq_zero.mpr ha)) |
      exact False.elim (hj hz.1) |
      exact False.elim (hj (neg_eq_zero.mpr hz.1)) |
      exact False.elim (hj hz.2) |
      exact False.elim (hj (neg_eq_zero.mpr hz.2))

  ·
    refine ⟨7, ?_⟩
    intro j hj
    fin_cases j
    all_goals first | exact Or.inl rfl |
      exact Or.inr rfl |
      exact False.elim (hj rfl) |
      exact False.elim (hj ha) |
      exact False.elim (hj (neg_eq_zero.mpr ha)) |
      exact False.elim (hj hz.1) |
      exact False.elim (hj (neg_eq_zero.mpr hz.1)) |
      exact False.elim (hj hz.2) |
      exact False.elim (hj (neg_eq_zero.mpr hz.2))

private theorem reduce_orbit_21 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 21))
    (hc : AllTwoCopySafe (fullOrbit u 21) t) : OneComplementPair (fullOrbit u 21) := by
  have hz : fullOrbit u 21 = 0 := dense21_from_arrays ![u 0,u 1,u 2,u 3,u 4] t ht
    (hc (denseSpecs 1) (dense_specs_valid 1))
    (hc (denseSpecs 2) (dense_specs_valid 2))
  refine ⟨0, ?_⟩
  intro j hj
  exact False.elim (hj (congrFun hz j))

private theorem reduce_orbit_22 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 22))
    (hc : AllTwoCopySafe (fullOrbit u 22) t) : OneComplementPair (fullOrbit u 22) := by
  have hz : fullOrbit u 22 = 0 := dense22_from_arrays ![u 0,u 1,u 2,u 3,u 4] t ht
    (hc (denseSpecs 3) (dense_specs_valid 3))
    (hc (denseSpecs 4) (dense_specs_valid 4))
    (hc (denseSpecs 5) (dense_specs_valid 5))
  refine ⟨0, ?_⟩
  intro j hj
  exact False.elim (hj (congrFun hz j))

private theorem reduce_orbit_23 (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe (fullOrbit u 23))
    (hc : AllTwoCopySafe (fullOrbit u 23) t) : OneComplementPair (fullOrbit u 23) := by
  have hz := dense23_from_arrays ![u 0,u 1,u 2,u 3,u 4] t ht
    (hc (denseSpecs 6) (dense_specs_valid 6))
    (hc (denseSpecs 7) (dense_specs_valid 7))
    (hc (denseSpecs 8) (dense_specs_valid 8))
  exact ⟨9, hz⟩

/-- Every official signed row satisfies A.4's support conclusion, assuming
all actual loop and two-copy arrays pass the necessary safety equations. -/
theorem all_orbits_one_complement_pair (u : Fin 8 → K) (t : K) (ht : t ≠ 0)
    (r : Fin 24) (hl : AllLoopSafe (fullOrbit u r))
    (hc : AllTwoCopySafe (fullOrbit u r) t) : OneComplementPair (fullOrbit u r) := by
  fin_cases r
  · exact reduce_orbit_0 u t ht hl hc
  · exact reduce_orbit_1 u t ht hl hc
  · exact reduce_orbit_2 u t ht hl hc
  · exact reduce_orbit_3 u t ht hl hc
  · exact reduce_orbit_4 u t ht hl hc
  · exact reduce_orbit_5 u t ht hl hc
  · exact reduce_orbit_6 u t ht hl hc
  · exact reduce_orbit_7 u t ht hl hc
  · exact reduce_orbit_8 u t ht hl hc
  · exact reduce_orbit_9 u t ht hl hc
  · exact reduce_orbit_10 u t ht hl hc
  · exact reduce_orbit_11 u t ht hl hc
  · exact reduce_orbit_12 u t ht hl hc
  · exact reduce_orbit_13 u t ht hl hc
  · exact reduce_orbit_14 u t ht hl hc
  · exact reduce_orbit_15 u t ht hl hc
  · exact reduce_orbit_16 u t ht hl hc
  · exact reduce_orbit_17 u t ht hl hc
  · exact reduce_orbit_18 u t ht hl hc
  · exact reduce_orbit_19 u t ht hl hc
  · exact reduce_orbit_20 u t ht hl hc
  · exact reduce_orbit_21 u t ht hl hc
  · exact reduce_orbit_22 u t ht hl hc
  · exact reduce_orbit_23 u t ht hl hc

end Paper2.Certificates.Q6
