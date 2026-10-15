import Paper2.Paper1Accepted.PhasePencil

/-! Four-port odd-dihedral coefficient classification. The RN relation is
the precise already-known cyclic pencil lemma; all consequences that use the
additional reflected pencils and odd group order are proved here. -/
namespace Paper2.HeightOne.Dihedral
open PhasePencil Tractable
noncomputable section

lemma root_ne_zero {N : ℕ} (hN : 0 < N) {a : AlgebraicComplex} (ha : Root N a) : a ≠ 0 := by
  intro hz
  simp [Root, hz, Nat.ne_of_gt hN] at ha

lemma root_mul {N : ℕ} {a b : AlgebraicComplex} (ha : Root N a) (hb : Root N b) :
    Root N (a * b) := by
  change (a * b) ^ N = 1
  rw [mul_pow, ha, hb, one_mul]

lemma root_neg_disjoint {N : ℕ} (hodd : Odd N) {a : AlgebraicComplex}
    (ha : Root N a) : ¬ Root N (-a) := by
  intro hb
  have hh : (1 : AlgebraicComplex) = -1 := by
    calc
      1 = (-a) ^ N := hb.symm
      _ = -(a ^ N) := hodd.neg_pow a
      _ = -1 := by rw [ha]
  norm_num at hh

lemma root_not_negative_product {N : ℕ} (hodd : Odd N)
    {a b c : AlgebraicComplex} (ha : Root N a) (hb : Root N b) (hc : Root N c) :
    a ≠ -b * c := by
  intro he
  apply root_neg_disjoint hodd (root_mul hb hc)
  simpa [he] using ha

/-- Two complementary equal-kernel decks synchronize zero/nonzero endpoints. -/
theorem paired_relation_endpoints {N : ℕ} (hN : 0 < N) {p x y t : AlgebraicComplex}
    (hxy : Relation N p x y t) (hyx : Relation N p y x t) : p = 0 ↔ t = 0 := by
  obtain ⟨a, ha, h₁ | h₁ | h₁⟩ := hxy
  · have hna := root_ne_zero hN ha
    obtain ⟨b, hb, h₂ | h₂ | h₂⟩ := hyx
    · have hnb := root_ne_zero hN hb
      rw [h₁.2, h₂.1]
      simp [hna, hnb]
    · have hp : p = 0 := (mul_eq_zero.mp (h₁.1.symm.trans h₂.1)).resolve_left
        (neg_ne_zero.mpr hna)
      have ht : t = 0 := by rw [h₁.2, h₂.2.1, mul_zero]
      simp [hp, ht]
    · simp [h₂.1, h₂.2.1]
  · have hna := root_ne_zero hN ha
    rw [h₁.2.2]
    simp [hna]
  · simp [h₁.1, h₁.2.1]

/-- If an endpoint is live, every live complementary block has negative phase
ratios from it, and its product equals the endpoint product. -/
theorem paired_relation_live {N : ℕ} (hN : 0 < N) {p x y t : AlgebraicComplex}
    (hp : p ≠ 0) (hxy : Relation N p x y t) (hyx : Relation N p y x t) :
    t ≠ 0 ∧ (∃ r, Root N r ∧ t = r * p) ∧
      ((x = 0 ∧ y = 0) ∨ ∃ a b, Root N a ∧ Root N b ∧
        x = -a * p ∧ y = -b * p ∧ t = (a * b) * p) := by
  have ht : t ≠ 0 := fun h => hp ((paired_relation_endpoints hN hxy hyx).mpr h)
  refine ⟨ht, ?_⟩
  obtain ⟨a, ha, h₁ | h₁ | h₁⟩ := hxy
  · obtain ⟨b, hb, h₂ | h₂ | h₂⟩ := hyx
    · have he : t = (b * a) * p := by rw [h₁.2, h₂.1]; ring
      exact ⟨⟨b * a, root_mul hb ha, he⟩,
        Or.inr ⟨b, a, hb, ha, h₂.1, h₁.1, he⟩⟩
    · exact False.elim (hp ((mul_eq_zero.mp (h₁.1.symm.trans h₂.1)).resolve_left
        (neg_ne_zero.mpr (root_ne_zero hN ha))))
    · exact False.elim (hp h₂.1)
  · exact ⟨⟨a, ha, h₁.2.2⟩, Or.inl ⟨h₁.1, h₁.2.1⟩⟩
  · exact False.elim (hp h₁.1)

/-- Four nonzero entries leave only the proportional RN alternative. -/
lemma relation_live_proportional {N : ℕ} {a b c d : AlgebraicComplex}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : Relation N a b c d) :
    ∃ r, Root N r ∧ c = -r * a ∧ d = -r * b := by
  obtain ⟨r, hr, hp | hd | hm⟩ := h
  · exact ⟨r, hr, hp⟩
  · exact False.elim (hb hd.1)
  · exact False.elim (ha hm.1)

/-- Reflected pencils cannot connect two live negative-phase blocks at odd N. -/
theorem no_two_live_negative_blocks {N : ℕ} (hodd : Odd N)
    {p a b c d : AlgebraicComplex} (hp : p ≠ 0)
    (ha : Root N a) (hb : Root N b) (hc : Root N c) (hd : Root N d) :
    ¬ Relation N (-a * p) (-b * p) (-c * p) (-d * p) := by
  have hN : 0 < N := hodd.pos
  intro h
  obtain ⟨r, hr, hcr, _⟩ := relation_live_proportional
    (mul_ne_zero (neg_ne_zero.mpr (root_ne_zero hN ha)) hp)
    (mul_ne_zero (neg_ne_zero.mpr (root_ne_zero hN hb)) hp) h
  have he : c = -r * a := by
    apply (mul_right_cancel₀ hp)
    linear_combination -hcr
  exact root_not_negative_product hodd hc hr ha he


lemma root_div {N : ℕ} {a b : AlgebraicComplex} (ha : Root N a) (hb : Root N b) :
    Root N (a / b) := by
  change (a / b) ^ N = 1
  rw [div_pow, ha, hb, div_one]

/-- With zero endpoints, each complementary pair has a positive phase ratio,
including the zero pair. -/
theorem relation_zero_endpoints {N : ℕ} (hN : 0 < N) {x y : AlgebraicComplex}
    (h : Relation N 0 x y 0) : ∃ a, Root N a ∧ y = a * x := by
  obtain ⟨a, ha, hp | hd | hm⟩ := h
  · have hx : x = 0 := (mul_eq_zero.mp hp.2.symm).resolve_left
      (neg_ne_zero.mpr (root_ne_zero hN ha))
    exact ⟨1, by simp [Root], by simpa [hx] using hp.1⟩
  · exact ⟨1, by simp [Root], by simp [hd.1, hd.2.1]⟩
  · exact ⟨a, ha, hm.2.2⟩

/-- A live reflected card forces a negative phase ratio between the two
chosen complementary-block leading coefficients. -/
theorem reflected_negative_ratio {N : ℕ} (hN : 0 < N)
    {x z a b : AlgebraicComplex} (hx : x ≠ 0) (hz : z ≠ 0)
    (ha : Root N a) (hb : Root N b)
    (h : Relation N x z (b * z) (a * x)) :
    ∃ r, Root N r ∧ z = -r * x := by
  obtain ⟨r, hr, he, _⟩ := relation_live_proportional hx hz h
  refine ⟨r / b, root_div hr hb, ?_⟩
  have hb0 := root_ne_zero hN hb
  apply (mul_left_cancel₀ hb0)
  rw [he]
  field_simp

lemma no_negative_root_triangle {N : ℕ} (hodd : Odd N)
    {x y z : AlgebraicComplex} (hx : x ≠ 0)
    (hxy : ∃ a, Root N a ∧ y = -a * x)
    (hxz : ∃ b, Root N b ∧ z = -b * x)
    (hyz : ∃ c, Root N c ∧ z = -c * y) : False := by
  obtain ⟨a, ha, heya⟩ := hxy
  obtain ⟨b, hb, hezb⟩ := hxz
  obtain ⟨c, hc, hezc⟩ := hyz
  have he : b = -c * a := by
    apply (mul_right_cancel₀ hx)
    rw [heya] at hezc
    linear_combination hezb - hezc
  exact root_not_negative_product hodd hb hc ha he

/-- The additional reflected equations are genuinely Paper 2 constraints.
The three rows are the three central complementary pairs of an even table. -/
def QuaternaryRelations (N : ℕ) (p t : AlgebraicComplex)
    (x y : Fin 3 → AlgebraicComplex) : Prop :=
  (∀ i, Relation N p (x i) (y i) t ∧ Relation N p (y i) (x i) t) ∧
  (∀ i j, i ≠ j → Relation N (x i) (x j) (y j) (y i))

/-- A live endpoint leaves at most one live central complementary pair.
The coefficient formula retains its two independent root phases. -/
theorem quaternary_live_endpoint {N : ℕ} (hodd : Odd N)
    {p t : AlgebraicComplex} {x y : Fin 3 → AlgebraicComplex}
    (hp : p ≠ 0) (h : QuaternaryRelations N p t x y) :
    t ≠ 0 ∧ (∃ r, Root N r ∧ t = r * p) ∧
      (∀ i, (x i = 0 ∧ y i = 0) ∨ ∃ a b, Root N a ∧ Root N b ∧
        x i = -a * p ∧ y i = -b * p ∧ t = (a * b) * p) ∧
      (∀ i j, x i ≠ 0 → x j ≠ 0 → i = j) := by
  have hrow := fun i => paired_relation_live hodd.pos hp (h.1 i).1 (h.1 i).2
  refine ⟨(hrow 0).1, (hrow 0).2.1, fun i => (hrow i).2.2, ?_⟩
  intro i j hi hj
  by_contra hij
  obtain hi0 | ⟨a, b, ha, hb, hxi, hyi, hti⟩ := (hrow i).2.2
  · exact hi hi0.1
  obtain hj0 | ⟨c, d, hc, hd, hxj, hyj, htj⟩ := (hrow j).2.2
  · exact hj hj0.1
  have hr := h.2 i j hij
  rw [hxi, hyi, hxj, hyj] at hr
  exact no_two_live_negative_blocks hodd hp ha hc hd hb hr

/-- With zero endpoints the reflected triangle forbids three live central
pairs. This also proves the odd-order exclusion without any support certificate. -/
theorem quaternary_zero_endpoints {N : ℕ} (hodd : Odd N)
    {x y : Fin 3 → AlgebraicComplex} (h : QuaternaryRelations N 0 0 x y) :
    (∀ i, ∃ a, Root N a ∧ y i = a * x i) ∧
      (x 0 = 0 ∨ x 1 = 0 ∨ x 2 = 0) := by
  have hr (i : Fin 3) := relation_zero_endpoints hodd.pos (h.1 i).1
  refine ⟨hr, ?_⟩
  by_contra hnone
  push_neg at hnone
  obtain ⟨a₀, ha₀, he₀⟩ := hr 0
  obtain ⟨a₁, ha₁, he₁⟩ := hr 1
  obtain ⟨a₂, ha₂, he₂⟩ := hr 2
  have h01 := h.2 0 1 (by decide)
  have h02 := h.2 0 2 (by decide)
  have h12 := h.2 1 2 (by decide)
  rw [he₀, he₁] at h01
  rw [he₀, he₂] at h02
  rw [he₁, he₂] at h12
  exact no_negative_root_triangle hodd hnone.1
    (reflected_negative_ratio hodd.pos hnone.1 hnone.2.1 ha₀ ha₁ h01)
    (reflected_negative_ratio hodd.pos hnone.1 hnone.2.2 ha₀ ha₂ h02)
    (reflected_negative_ratio hodd.pos hnone.2.1 hnone.2.2 ha₁ ha₂ h12)

end
end Paper2.HeightOne.Dihedral
