import Paper2.HeightOne.Cyclic.QuaternaryPhases

/-! The final algebraic obstruction in the zero-endpoint, three-live-pair
cyclic four-port case.  These statements describe the row of the actual
two-copy output; graph realization and its Walsh row are separate obligations.
-/
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable PhasePencil Dihedral

lemma odd_root_square_one {N : ℕ} (hodd : Odd N) {a : AlgebraicComplex}
    (ha : Root N a) (h2 : a ^ 2 = 1) : a = 1 := by
  rcases sq_eq_one_iff.mp h2 with h | h
  · exact h
  · apply False.elim
    exact (root_neg_disjoint hodd (by simp [Root] : Root N (1 : AlgebraicComplex)))
      (by simpa only [h] using ha)

/-- Equal nonzero endpoints and an equal complementary central pair force
the phase to one at odd order.  This is the exact constraint used on G_i. -/
theorem symmetric_live_row {N : ℕ} (hodd : Odd N) {p z : AlgebraicComplex}
    (hp : p ≠ 0) (h : Relation N p z z p) : z = 0 ∨ z = -p := by
  obtain ⟨_, _, hz | ⟨a, b, ha, hb, hza, hzb, hpab⟩⟩ :=
    paired_relation_live hodd.pos hp h h
  · exact Or.inl hz.1
  · right
    have hab : a = b := by
      apply mul_right_cancel₀ hp
      linear_combination hza - hzb
    have hab1 : a * b = 1 := by
      apply mul_right_cancel₀ hp
      simpa using hpab.symm
    have ha2 : a ^ 2 = 1 := by simpa [← hab, pow_two] using hab1
    rw [odd_root_square_one hodd ha ha2] at hza
    simpa using hza

def nextPair : Fin 3 → Fin 3 := ![1, 2, 0]
def lastPair : Fin 3 → Fin 3 := ![2, 0, 1]

lemma three_pair_squares_nonzero (sigma : Fin 3 → AlgebraicComplex)
    (hnz : ∀ i, sigma i ≠ 0) :
    ∃ i : Fin 3, sigma (nextPair i) ^ 2 + sigma (lastPair i) ^ 2 ≠ 0 := by
  by_contra h
  push_neg at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [nextPair, lastPair] at h0 h1 h2
  have hz : 2 * sigma 0 ^ 2 = 0 := by linear_combination h1 + h2 - h0
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (hnz 0)) hz

/-- At least one complementary deletion row of the two-copy array fails the
cyclic RN law.  The hypothesis is the literal sum-zero condition on all three
live scalar pairs; no unsafe-output oracle is assumed. -/
theorem zero_sum_three_pairs_obstruction {N : ℕ} (hodd : Odd N)
    (sigma : Fin 3 → AlgebraicComplex) (hnz : ∀ i, sigma i ≠ 0)
    (hsum : sigma 0 + sigma 1 + sigma 2 = 0) :
    ∃ i : Fin 3, ¬ Relation N (sigma i ^ 2)
      (-(sigma (nextPair i) ^ 2 + sigma (lastPair i) ^ 2))
      (-(sigma (nextPair i) ^ 2 + sigma (lastPair i) ^ 2)) (sigma i ^ 2) := by
  obtain ⟨i, hi⟩ := three_pair_squares_nonzero sigma hnz
  refine ⟨i, ?_⟩
  intro hrow
  have hp := pow_ne_zero 2 (hnz i)
  have hz : -(sigma (nextPair i) ^ 2 + sigma (lastPair i) ^ 2) ≠ 0 := neg_ne_zero.mpr hi
  have he := (symmetric_live_row hodd hp hrow).resolve_left hz
  have hs : sigma i = -(sigma (nextPair i) + sigma (lastPair i)) := by
    fin_cases i <;> simp [nextPair, lastPair] <;> linear_combination hsum
  have hab : 2 * sigma (nextPair i) * sigma (lastPair i) = 0 := by
    rw [hs] at he
    linear_combination he
  exact mul_ne_zero (mul_ne_zero (by norm_num) (hnz _)) (hnz _) hab

end
end Paper2.HeightOne.Cyclic
