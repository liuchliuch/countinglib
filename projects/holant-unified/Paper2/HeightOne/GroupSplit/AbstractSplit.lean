import Paper2.HeightOne.GroupSplit.Accepted

/-! Group-theoretic elimination before any matrix normalization. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.GroupSplit
open FiniteGroupFacts
noncomputable section

variable {A B : Type*} [Group A] [Group B]

def Covered (J : Subgroup A) (z : A) : Prop := ∀ x : A, x ∈ J ∨ z * x ∈ J

def ExtraInvolution (J : Subgroup A) (z : A) : Prop :=
  ∃ u ∈ J, u * u = 1 ∧ u ≠ 1 ∧ u ≠ z ∧ Commute u z

lemma covered_eq_top_or_index_two (J : Subgroup A) (z : A) (hz : z * z = 1)
    (hcover : Covered J z) : J = ⊤ ∨ J.index = 2 := by
  by_cases hzin : z ∈ J
  · left
    apply top_unique
    intro x _
    rcases hcover x with hx | hx
    · exact hx
    · have h := J.mul_mem hzin hx
      simpa only [← mul_assoc, hz, one_mul] using h
  · right
    exact Subgroup.index_eq_two_iff_exists_notMem_and'.mpr
      ⟨z, hzin, fun x => (hcover x).symm⟩

lemma Covered.map {J : Subgroup A} {z : A} (h : Covered J z) (e : A ≃* B) :
    Covered (J.map e.toMonoidHom) (e z) := by
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rcases h x with hx | hx
  · exact Or.inl ⟨x, hx, rfl⟩
  · exact Or.inr ⟨z * x, hx, e.map_mul _ _⟩

lemma ExtraInvolution.of_map {J : Subgroup A} {z : A} (e : A ≃* B)
    (h : ExtraInvolution (J.map e.toMonoidHom) (e z)) : ExtraInvolution J z := by
  obtain ⟨u, ⟨v, hv, rfl⟩, hsq, h1, hz, hcomm⟩ := h
  refine ⟨v, hv, e.injective ?_, ?_, ?_, ?_⟩
  · simpa only [map_mul, map_one, MulEquiv.coe_toMonoidHom] using hsq
  · intro h; exact h1 (h ▸ e.map_one)
  · intro h; exact hz (congrArg e h)
  · apply e.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using hcomm.eq

lemma a4_covered_extra (J : Subgroup A4) (z : A4)
    (hz : z * z = 1) (hne : z ≠ 1) (hcover : Covered J z) : ExtraInvolution J z := by
  have htop : J = ⊤ := (covered_eq_top_or_index_two J z hz hcover).resolve_right
    (a4_no_index_two J)
  obtain ⟨u, hs, h1, huz, hc⟩ := a4_extra_involution z hz hne
  exact ⟨u, htop ▸ Subgroup.mem_top u, hs, h1, huz, hc⟩

lemma a5_covered_extra (J : Subgroup A5) (z : A5)
    (hz : z * z = 1) (hne : z ≠ 1) (hcover : Covered J z) : ExtraInvolution J z := by
  have htop : J = ⊤ := (covered_eq_top_or_index_two J z hz hcover).resolve_right
    (a5_no_index_two J)
  obtain ⟨u, hs, h1, huz, hc⟩ := a5_extra_involution z hz hne
  exact ⟨u, htop ▸ Subgroup.mem_top u, hs, h1, huz, hc⟩

lemma s4_covered_extra (J : Subgroup S4) (z : S4)
    (hz : z * z = 1) (hne : z ≠ 1) (hcover : Covered J z) : ExtraInvolution J z := by
  obtain ⟨u, hs, h1, huz, hc, heven⟩ := s4_extra_even_involution z hz hne
  have hu : u ∈ J := by
    rcases covered_eq_top_or_index_two J z hz hcover with htop | hi
    · exact htop ▸ Subgroup.mem_top u
    · simpa only [Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi] using heven
  exact ⟨u, hu, hs, h1, huz, hc⟩

lemma rotation_involution_central {n : ℕ} {i : ZMod n}
    (h : DihedralGroup.r i * DihedralGroup.r i = 1) :
    ∀ x : DihedralGroup n, Commute x (DihedralGroup.r i) := by
  have hi : i + i = 0 := DihedralGroup.r.inj h
  have hneg : -i = i := by linear_combination -hi
  rintro (j | j)
  · change DihedralGroup.r (j + i) = DihedralGroup.r (i + j)
    rw [add_comm]
  · change DihedralGroup.sr (j + i) = DihedralGroup.sr (j - i)
    rw [sub_eq_add_neg, hneg]

/-- Even rotations supply a central involution. One of it and its z-coset
partner belongs to J, and both are eligible extra involutions. -/
lemma even_dihedral_covered_extra {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (J : Subgroup (DihedralGroup n)) (i : ZMod n)
    (hcover : Covered J (DihedralGroup.sr i)) : ExtraInvolution J (DihedralGroup.sr i) := by
  letI : NeZero n := ⟨by omega⟩
  have hevenR : Even (Nat.card (Dihedral.rotations n)) := by
    simpa only [Dihedral.rotations_card] using heven
  obtain ⟨u, huorder⟩ :=
    (cyclic_exists_involution_iff_even (G := Dihedral.rotations n)).mpr hevenR
  have huorder' : orderOf (u : DihedralGroup n) = 2 := by simpa using huorder
  have husq : (u : DihedralGroup n) * u = 1 := by
    simpa only [pow_two, huorder'] using pow_orderOf_eq_one (u : DihedralGroup n)
  have huone : (u : DihedralGroup n) ≠ 1 := by
    intro h; simp [h] at huorder'
  obtain ⟨j, hj⟩ := u.property
  have huz : (u : DihedralGroup n) ≠ DihedralGroup.sr i := by simp [hj]
  have hc : ∀ x : DihedralGroup n, Commute x (u : DihedralGroup n) := by
    rw [hj] at husq ⊢
    exact rotation_involution_central husq
  rcases hcover u with hu | hu
  · exact ⟨u, hu, husq, huone, huz, (hc _).symm⟩
  · let z := DihedralGroup.sr i
    have hzsq : z * z = 1 := by simp [z]
    refine ⟨z * u, hu, ?_, ?_, ?_, ?_⟩
    · calc
        (z * u) * (z * u) = z * (u * z) * u := by group
        _ = z * (z * u) * u := by rw [(hc z).eq.symm]
        _ = (z * z) * (u * u) := by group
        _ = 1 := by rw [hzsq, husq, one_mul]
    · intro h
      have hh := congrArg (fun v => z * v) h
      have hueq : (u : DihedralGroup n) = z := by simpa only [← mul_assoc, hzsq, one_mul, mul_one] using hh
      exact huz hueq
    · intro h
      exact huone (mul_left_cancel (h.trans (mul_one z).symm))
    · exact (Commute.refl z).mul_left (hc z).symm


/-- The remaining abstract alternative identifies the distinguished element as
an actual reflection and the subgroup as all rotations or the full dihedral group. -/
def OddDihedralPresentation (J : Subgroup A) (z : A) : Prop :=
  ∃ N : ℕ, 3 ≤ N ∧ Odd N ∧ ∃ e : A ≃* DihedralGroup N,
    (∃ i : ZMod N, e z = DihedralGroup.sr i) ∧
    (J.map e.toMonoidHom = Dihedral.rotations N ∨ J.map e.toMonoidHom = ⊤)

/-- The complete abstract case elimination from the five finite PGL types.
No matrix basis and no Paper 2 split conclusion occurs in the hypotheses. -/
theorem finite_group_reduction (J : Subgroup A) (z : A)
    (hz : z * z = 1) (hne : z ≠ 1) (hcover : Covered J z)
    (htypes : FinitePGLTypes A) :
    (∀ x ∈ J, Commute x z) ∨ ExtraInvolution J z ∨ OddDihedralPresentation J z := by
  have mapped_sq {B : Type} [Group B] (e : A ≃* B) : e z * e z = 1 := by rw [← map_mul, hz, map_one]
  have mapped_ne {B : Type} [Group B] (e : A ≃* B) : e z ≠ 1 := by
    intro h
    apply hne
    apply e.injective
    simpa only [map_one] using h
  unfold FinitePGLTypes at htypes
  rcases htypes with hcyc | hd | ha4 | hs4 | ha5
  · letI : IsCyclic A := hcyc
    left
    intro x _
    exact IsMulCommutative.is_comm.comm x z
  · obtain ⟨N, hN, ⟨e⟩⟩ := hd
    have hc := hcover.map e
    cases hez : e z with
    | r i =>
      left
      intro x _
      apply e.injective
      simpa only [map_mul, hez] using
        (rotation_involution_central (hez ▸ mapped_sq e) (e x)).eq
    | sr i =>
      by_cases heven : Even N
      · right; left
        apply ExtraInvolution.of_map e
        rw [hez]
        exact even_dihedral_covered_extra hN heven _ i (hez ▸ hc)
      · right; right
        have hodd : Odd N := Nat.not_even_iff_odd.mp heven
        have hN3 : 3 ≤ N := by obtain ⟨k, hk⟩ := hodd; omega
        refine ⟨N, hN3, hodd, e, ⟨i, hez⟩, ?_⟩
        rcases covered_eq_top_or_index_two _ (e z) (mapped_sq e) hc with htop | hi
        · exact Or.inr htop
        · exact Or.inl (Dihedral.odd_unique_index_two hodd _ hi)
  · obtain ⟨e⟩ := ha4
    right; left
    apply ExtraInvolution.of_map e
    exact a4_covered_extra _ _ (mapped_sq e) (mapped_ne e) (hcover.map e)
  · obtain ⟨e⟩ := hs4
    right; left
    apply ExtraInvolution.of_map e
    exact s4_covered_extra _ _ (mapped_sq e) (mapped_ne e) (hcover.map e)
  · obtain ⟨e⟩ := ha5
    right; left
    apply ExtraInvolution.of_map e
    exact a5_covered_extra _ _ (mapped_sq e) (mapped_ne e) (hcover.map e)

end
end Paper2.HeightOne.GroupSplit
