import Paper2.Certificates.Q6Dense

/-! Direct field-independent elimination for sparse orbit families 2--6.
These lemmas replace the relevant projective-chart search by exact algebra.
The symbolic loop/card hypotheses are explicit; finite correspondence with
arbitrary signed-space vectors and the full orbit cover are separate. -/
namespace Paper2.Certificates.Q6

variable {K : Type*} [CommRing K] [NoZeroDivisors K] [CharZero K]

omit [CharZero K] in
/-- Reversing W₄ order leaves all necessary conditions unchanged. -/
theorem NecessarySafe.reverse {v : Fin 6 → K} (h : NecessarySafe v) :
    NecessarySafe ![v 5, v 4, v 3, v 2, v 1, v 0] := by
  refine ⟨h.zero05.symm, h.zero14.symm, h.zero23.symm, ?_, ?_, ?_, ?_⟩
  · simpa [mul_comm] using h.zeroProduct
  · simpa [mul_comm] using h.products01
  · simpa [mul_comm] using h.products02
  · simpa [mul_comm] using h.products12

omit [CharZero K] in
/-- Sparse orbit 2: the first loop links the two parameters, and the selected
card rules out both being nonzero. -/
theorem sparse2_zero (t a b : K) (ht : t ≠ 0)
    (hl : NecessarySafe ![b, -b, 0, 0, a, -a])
    (hc : NecessarySafe ![t, b^2, -a*b, -a*b, a^2, t]) : a = 0 ∧ b = 0 := by
  have hba : b = 0 ↔ a = 0 := by simpa using hl.zero05
  by_cases ha : a = 0
  · exact ⟨ha, hba.mpr ha⟩
  · have hb : b ≠ 0 := fun h => ha (hba.mp h)
    exact False.elim (not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, ha, hb]) hc)

omit [CharZero K] in
/-- Sparse orbit 3 leaves one of its two complementary blocks. -/
theorem sparse3_one_pair (t a b c d : K) (ht : t ≠ 0)
    (hl : NecessarySafe ![c, d, 0, 0, a, b])
    (hc : NecessarySafe ![t, d^2, b*c, b*c, a^2, t]) :
    (a = 0 ∧ d = 0) ∨ (b = 0 ∧ c = 0) := by
  have hcb : c = 0 ↔ b = 0 := hl.zero05
  have hda : d = 0 ↔ a = 0 := hl.zero14
  by_cases ha : a = 0
  · exact Or.inl ⟨ha, hda.mpr ha⟩
  · have hd : d ≠ 0 := fun h => ha (hda.mp h)
    by_cases hb : b = 0
    · exact Or.inr ⟨hb, hcb.mpr hb⟩
    · have hc0 : c ≠ 0 := fun h => hb (hcb.mp h)
      exact False.elim (not_safe_full_support _ (by
        intro i
        fin_cases i <;> simp [ht, ha, hb, hc0, hd]) hc)

/-- Sparse orbit 4 is zero from its identity card alone. -/
theorem sparse4_zero (t a : K) (ht : t ≠ 0)
    (hc : NecessarySafe ![t, 2*a^2, -3*a^2, -3*a^2, 2*a^2, t]) : a = 0 := by
  by_contra ha
  exact not_safe_full_support _ (by
    intro i
    fin_cases i <;> simp [ht, ha]) hc

/-- Sparse orbit 5 has the same loop-link/full-support obstruction. -/
theorem sparse5_zero (t a b : K) (ht : t ≠ 0)
    (hl : NecessarySafe ![b, 0, a-b, a-b, 0, -a])
    (hc : NecessarySafe ![t, 2*b^2, -3*a*b, -3*a*b, 2*a^2, t]) : a = 0 ∧ b = 0 := by
  have hba : b = 0 ↔ a = 0 := by simpa using hl.zero05
  by_cases ha : a = 0
  · exact ⟨ha, hba.mpr ha⟩
  · have hb : b ≠ 0 := fun h => ha (hba.mp h)
    exact False.elim (not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, ha, hb]) hc)

omit [CharZero K] in
/-- Sparse orbit 6 leaves only its a,d complementary block. -/
theorem sparse6_one_pair (t a b c d : K) (ht : t ≠ 0)
    (hl : NecessarySafe ![c, 0, a-c, b+d, 0, -b])
    (hc : NecessarySafe ![t, -c^2, c^2, b^2, -b^2, t]) : b = 0 ∧ c = 0 := by
  have hcb : c = 0 ↔ b = 0 := by simpa using hl.zero05
  by_cases hb : b = 0
  · exact ⟨hb, hcb.mpr hb⟩
  · have hc0 : c ≠ 0 := fun h => hb (hcb.mp h)
    exact False.elim (not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, hb, hc0]) hc)


omit [CharZero K] in
/-- A single selected card links the two squared parameters and rules out
both being nonzero. This covers sparse orbits 2,5,8 and the residual orbit 16. -/
theorem square_product_card_zero (t a b n m : K) (ht : t ≠ 0)
    (hn : n ≠ 0) (hm : m ≠ 0)
    (hs : NecessarySafe ![t, n*b^2, m*a*b, m*a*b, n*a^2, t]) :
    a = 0 ∧ b = 0 := by
  have hba : b = 0 ↔ a = 0 := by simpa [hn] using hs.zero14
  by_cases ha : a = 0
  · exact ⟨ha, hba.mpr ha⟩
  · have hb : b ≠ 0 := fun h => ha (hba.mp h)
    exact False.elim (not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, ha, hb, hn, hm]) hs)

omit [CharZero K] in
/-- The alternate squared card covers sparse orbit 6 and residual orbit 19. -/
theorem square_square_card_zero (t a b n m : K) (ht : t ≠ 0)
    (hn : n ≠ 0) (hm : m ≠ 0)
    (hs : NecessarySafe ![t, n*b^2, m*b^2, m*a^2, n*a^2, t]) :
    a = 0 ∧ b = 0 := by
  have hba : b = 0 ↔ a = 0 := by simpa [hn] using hs.zero14
  by_cases ha : a = 0
  · exact ⟨ha, hba.mpr ha⟩
  · have hb : b ≠ 0 := fun h => ha (hba.mp h)
    exact False.elim (not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, ha, hb, hn, hm]) hs)

/-- Sparse orbit 8 leaves its b,c complementary block. -/
theorem sparse8_one_pair (t a d : K) (ht : t ≠ 0)
    (hs : NecessarySafe ![t, 2*d^2, -2*a*d, -2*a*d, 2*a^2, t]) :
    a = 0 ∧ d = 0 :=
  square_product_card_zero t a d 2 (-2) ht (by norm_num) (by norm_num) hs

/-- The one-parameter families 11,12,13,15,17 and the principal part of
14,16,18,19 all reduce to this unequal-square obstruction. -/
theorem principal_two_six_zero (E a : K) (s r : Bool)
    (hs : NecessarySafe ![E, Bell.sign s * (2*a^2), Bell.sign r * (6*a^2),
      Bell.sign r * (6*a^2), Bell.sign s * (2*a^2), E]) : a = 0 := by
  apply unequal_middle_card E (Bell.sign s * 2) (Bell.sign r * 6) a
  · cases s <;> norm_num [Bell.sign]
  · cases r <;> norm_num [Bell.sign]
  · cases s <;> cases r <;> norm_num [Bell.sign]
  · simpa only [mul_assoc] using hs

/-- Sparse orbit 16 needs only cards 552 and 17, rather than a nonlinear
projective-chart solver. The first card kills a; the second kills b,c. -/
theorem sparse16_zero (t a b c E : K) (ht : t ≠ 0)
    (h552 : NecessarySafe ![E, -2*a^2, 6*a^2, 6*a^2, -2*a^2, E])
    (h17 : NecessarySafe ![t, 3*a^2-c^2, -a^2+a*b+a*c+b*c,
      -a^2-a*b-a*c+b*c, 3*a^2-b^2, t]) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have ha : a = 0 := unequal_middle_card E (-2) 6 a
    (by norm_num) (by norm_num) (by norm_num) h552
  have hr : NecessarySafe ![t, -c^2, b*c, b*c, -b^2, t] := by
    simpa [ha] using h17
  have hbc := square_product_card_zero t b c (-1) 1 ht (by norm_num) (by norm_num)
    (by simpa using hr)
  exact ⟨ha, hbc⟩

/-- Sparse orbit 19 likewise needs only cards 552 and 241. -/
theorem sparse19_zero (t a b c E : K) (ht : t ≠ 0)
    (h552 : NecessarySafe ![E, 2*a^2, -6*a^2, -6*a^2, 2*a^2, E])
    (h241 : NecessarySafe ![t, a^2+a*b+a*c-c^2, -a^2-a*b-a*c+c^2,
      -a^2-a*b-a*c+b^2, a^2+a*b+a*c-b^2, t]) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have ha := orbit20_principal_zero E a h552
  have hr : NecessarySafe ![t, -c^2, c^2, b^2, -b^2, t] := by
    simpa [ha] using h241
  have hbc := square_square_card_zero t b c (-1) 1 ht (by norm_num) (by norm_num)
    (by simpa using hr)
  exact ⟨ha, hbc⟩


omit [CharZero K] in
/-- A two-block loop and one card leave at most one complementary block. -/
theorem two_blocks_card (t b c d e : K) (ht : t ≠ 0)
    (hl : NecessarySafe ![0,d,e,b,c,0])
    (hc : NecessarySafe ![t,e^2,c*d,c*d,b^2,t]) :
    (b = 0 ∧ e = 0) ∨ (c = 0 ∧ d = 0) := by
  have hbe : b = 0 ↔ e = 0 := hl.zero23.symm
  have hcd : c = 0 ↔ d = 0 := hl.zero14.symm
  by_cases hb : b = 0
  · exact Or.inl ⟨hb, hbe.mp hb⟩
  · by_cases hc0 : c = 0
    · exact Or.inr ⟨hc0, hcd.mp hc0⟩
    · have he : e ≠ 0 := fun h => hb (hbe.mpr h)
      have hd : d ≠ 0 := fun h => hc0 (hcd.mpr h)
      exact False.elim (not_safe_full_support _ (by
        intro i
        fin_cases i <;> simp [ht, hb, hc0, hd, he]) hc)

end Paper2.Certificates.Q6
