import Paper2.Certificates.Q6Sparse

/-! The remaining large sparse families require only a graph on their
complementary blocks. Each edge is excluded by one full-support card; there
is no nonlinear real solver or normalization to a projective chart. -/
namespace Paper2.Certificates.Q6

variable {K : Type*} [CommRing K] [NoZeroDivisors K]

theorem one_block_of_pairwise {n : ℕ} [NeZero n] (a b : Fin n → K)
    (hlink : ∀ i, a i = 0 ↔ b i = 0)
    (hpair : ∀ i j, i ≠ j → a i ≠ 0 → a j ≠ 0 → False) :
    ∃ i : Fin n, ∀ j, j ≠ i → a j = 0 ∧ b j = 0 := by
  classical
  by_cases h : ∃ i, a i ≠ 0
  · obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_⟩
    intro j hji
    have hj : a j = 0 := by
      by_contra hj
      exact hpair i j (Ne.symm hji) hi hj
    exact ⟨hj, (hlink j).mp hj⟩
  · refine ⟨0, ?_⟩
    intro j _
    have hj : a j = 0 := by simpa using not_exists.mp h j
    exact ⟨hj, (hlink j).mp hj⟩

/-- Sparse family 7: three cards exclude the three pairs of active blocks. -/
theorem sparse7_one_block (t a b c d e f : K) (ht : t ≠ 0)
    (hl1 : NecessarySafe ![d,0,e,b,0,c])
    (hl2 : NecessarySafe ![d,f,0,0,a,c])
    (h17 : NecessarySafe ![t,e*f,b*e,b*e,a*b,t])
    (h80 : NecessarySafe ![t,d*f,d^2,c^2,a*c,t])
    (h92 : NecessarySafe ![t,d*e,d^2,c^2,b*c,t]) :
    ∃ i : Fin 3, ∀ j, j ≠ i → ![a,b,c] j = 0 ∧ ![f,e,d] j = 0 := by
  have haf : a = 0 ↔ f = 0 := hl2.zero14.symm
  have hbe : b = 0 ↔ e = 0 := hl1.zero23.symm
  have hcd : c = 0 ↔ d = 0 := hl1.zero05.symm
  have hab : a ≠ 0 → b ≠ 0 → False := by
    intro ha hb
    have hf : f ≠ 0 := fun h => ha (haf.mpr h)
    have he : e ≠ 0 := fun h => hb (hbe.mpr h)
    exact not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, ha, hb, he, hf]) h17
  have hac : a ≠ 0 → c ≠ 0 → False := by
    intro ha hc
    have hf : f ≠ 0 := fun h => ha (haf.mpr h)
    have hd : d ≠ 0 := fun h => hc (hcd.mpr h)
    exact not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, ha, hc, hd, hf]) h80
  have hbc : b ≠ 0 → c ≠ 0 → False := by
    intro hb hc
    have he : e ≠ 0 := fun h => hb (hbe.mpr h)
    have hd : d ≠ 0 := fun h => hc (hcd.mpr h)
    exact not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, hb, hc, hd, he]) h92
  apply one_block_of_pairwise
  · intro i
    fin_cases i
    · exact haf
    · exact hbe
    · exact hcd
  · intro i j hij hi hj
    fin_cases i <;> fin_cases j
    all_goals first | exact hij rfl | exact hab hi hj | exact hab hj hi |
      exact hac hi hj | exact hac hj hi | exact hbc hi hj | exact hbc hj hi

/-- Sparse family 9: the square-product card first kills the repeated block,
then the remaining card excludes its two residual blocks being active together. -/
theorem sparse9_one_block (t a b c d e f : K) (ht : t ≠ 0)
    (hl : NecessarySafe ![0,d,e,b,c,0])
    (h208 : NecessarySafe ![t,e^2,c*d,c*d,b^2,t])
    (h504 : NecessarySafe ![t,f^2,-a*f,-a*f,a^2,t]) :
    a = 0 ∧ f = 0 ∧
      ∃ i : Fin 2, ∀ j, j ≠ i → ![b,c] j = 0 ∧ ![e,d] j = 0 := by
  letI : Nontrivial K := nontrivial_of_ne t 0 ht
  have haf := square_product_card_zero t a f 1 (-1) ht one_ne_zero (neg_ne_zero.mpr one_ne_zero)
    (by simpa using h504)
  have hbe : b = 0 ↔ e = 0 := hl.zero23.symm
  have hcd : c = 0 ↔ d = 0 := hl.zero14.symm
  have hbc : b ≠ 0 → c ≠ 0 → False := by
    intro hb hc
    have he : e ≠ 0 := fun h => hb (hbe.mpr h)
    have hd : d ≠ 0 := fun h => hc (hcd.mpr h)
    exact not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, hb, hc, hd, he]) h208
  refine ⟨haf.1, haf.2, ?_⟩
  apply one_block_of_pairwise
  · intro i
    fin_cases i
    · exact hbe
    · exact hcd
  · intro i j hij hi hj
    fin_cases i <;> fin_cases j
    all_goals first | exact hij rfl | exact hbc hi hj | exact hbc hj hi

/-- Sparse family 10: its six cards exclude exactly the six edges of the
complete graph on the four complementary blocks. -/
theorem sparse10_one_block (t a b c d e f g h : K) (ht : t ≠ 0)
    (hl1 : NecessarySafe ![0,e,f,c,d,0])
    (hl2 : NecessarySafe ![0,g,h,a,b,0])
    (h18 : NecessarySafe ![t,f*g,c*f,c*f,b*c,t])
    (h21 : NecessarySafe ![t,e*h,d*e,d*e,a*d,t])
    (h208 : NecessarySafe ![t,f^2,d*e,d*e,c^2,t])
    (h355 : NecessarySafe ![t,e*g,e^2,d^2,b*d,t])
    (h356 : NecessarySafe ![t,f*h,f^2,c^2,a*c,t])
    (h504 : NecessarySafe ![t,h^2,b*g,b*g,a^2,t]) :
    ∃ i : Fin 4, ∀ j, j ≠ i → ![a,b,c,d] j = 0 ∧ ![h,g,f,e] j = 0 := by
  have hah : a = 0 ↔ h = 0 := hl2.zero23.symm
  have hbg : b = 0 ↔ g = 0 := hl2.zero14.symm
  have hcf : c = 0 ↔ f = 0 := hl1.zero23.symm
  have hde : d = 0 ↔ e = 0 := hl1.zero14.symm
  have hab : a ≠ 0 → b ≠ 0 → False := by
    intro ha hb
    have hh : h ≠ 0 := fun hz => ha (hah.mpr hz)
    have hg : g ≠ 0 := fun hz => hb (hbg.mpr hz)
    exact not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, ha, hb, hg, hh]) h504
  have hac : a ≠ 0 → c ≠ 0 → False := by
    intro ha hc
    have hh : h ≠ 0 := fun hz => ha (hah.mpr hz)
    have hf : f ≠ 0 := fun hz => hc (hcf.mpr hz)
    exact not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, ha, hc, hf, hh]) h356
  have had : a ≠ 0 → d ≠ 0 → False := by
    intro ha hd
    have hh : h ≠ 0 := fun hz => ha (hah.mpr hz)
    have he : e ≠ 0 := fun hz => hd (hde.mpr hz)
    exact not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, ha, hd, he, hh]) h21
  have hbc : b ≠ 0 → c ≠ 0 → False := by
    intro hb hc
    have hg : g ≠ 0 := fun hz => hb (hbg.mpr hz)
    have hf : f ≠ 0 := fun hz => hc (hcf.mpr hz)
    exact not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, hb, hc, hf, hg]) h18
  have hbd : b ≠ 0 → d ≠ 0 → False := by
    intro hb hd
    have hg : g ≠ 0 := fun hz => hb (hbg.mpr hz)
    have he : e ≠ 0 := fun hz => hd (hde.mpr hz)
    exact not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, hb, hd, he, hg]) h355
  have hcd : c ≠ 0 → d ≠ 0 → False := by
    intro hc hd
    have hf : f ≠ 0 := fun hz => hc (hcf.mpr hz)
    have he : e ≠ 0 := fun hz => hd (hde.mpr hz)
    exact not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, hc, hd, he, hf]) h208
  apply one_block_of_pairwise
  · intro i
    fin_cases i
    · exact hah
    · exact hbg
    · exact hcf
    · exact hde
  · intro i j hij hi hj
    fin_cases i <;> fin_cases j
    all_goals first | exact hij rfl | exact hab hi hj | exact hab hj hi |
      exact hac hi hj | exact hac hj hi | exact had hi hj | exact had hj hi |
      exact hbc hi hj | exact hbc hj hi | exact hbd hi hj | exact hbd hj hi |
      exact hcd hi hj | exact hcd hj hi

end Paper2.Certificates.Q6
