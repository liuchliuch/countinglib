import ComplexCSP.Recognition.Certificates

/-!
# Soundness of finite certificate branches

This proves the difficult zero-degeneration direction of the finite algebraic
locus description, conditional only on the explicit local intrinsic entry tests.
The tests must still be obtained from an actual legal purification construction.
-/

namespace ComplexCSP.Certificates

open scoped BigOperators
open BlockOrthogonality

variable {X D R K : Type*} [Fintype D] [DecidableEq D] [Field K]
variable {roots : RootAlphabet K R} {realize : ComplexRealization roots}
variable {c : Certificate X D R} {A : X → D → K} {P : X → D → ℂ}

omit [Fintype D] [DecidableEq D] in
private theorem sameRectangle_symm {x y : X} (h : c.SameRectangle x y) :
    c.SameRectangle y x := ⟨h.2 ▸ h.1, h.2.symm⟩

omit [Fintype D] in
private theorem purified_support_zero (hA : Satisfies roots c A)
    (hP : IntrinsicTests roots realize A P) (x : X) (z : D)
    (h : ¬ c.Allowed x z) : P x z = 0 :=
  (hP.zero x z).mpr (support_zero hA x z h)

omit [Fintype D] in
private theorem purified_nonzero_allowed (hA : Satisfies roots c A)
    (hP : IntrinsicTests roots realize A P) (x : X) (z : D)
    (h : P x z ≠ 0) : c.Allowed x z :=
  nonzero_allowed hA x z ((hP.zero x z).not.mp h)

omit [Fintype D] in
private theorem purified_outside_both (hA : Satisfies roots c A)
    (hP : IntrinsicTests roots realize A P) {x y : X} (hxy : c.SameRectangle x y)
    (z : D) (hz : ¬ c.Allowed x z) : P x z = 0 ∧ P y z = 0 := by
  refine ⟨purified_support_zero hA hP x z hz, purified_support_zero hA hP y z ?_⟩
  intro hy
  exact hz (c.allowed_other_row (sameRectangle_symm hxy) hy)

omit [Fintype D] in
/-- Every specialized certified rectangle has rank-one purified magnitudes on
its surviving support, including all zero entries and vanished subrectangles. -/
theorem certified_magnitude_proportional (hA : Satisfies roots c A)
    (hP : IntrinsicTests roots realize A P) {x y : X}
    (hxy : c.SameRectangle x y) (hx : P x ≠ 0) (hy : P y ≠ 0) :
    MagnitudeProportional (P x) (P y) := by
  apply (Purification.PurificationMap.magnitudeProportional_iff_minors hx hy).mpr
  intro z w
  by_cases hz : c.Allowed x z
  · by_cases hw : c.Allowed x w
    · exact (hP.magnitude_minor x y z w).mpr
        ⟨(c.pair x y).twist z w, twisted_minor hA x y z w hxy hz hw⟩
    · obtain ⟨hxw, hyw⟩ := purified_outside_both hA hP hxy w hw
      simp [hxw, hyw]
  · obtain ⟨hxz, hyz⟩ := purified_outside_both hA hP hxy z hz
    simp [hxz, hyz]

omit [Fintype D] in
/-- Support equations and twisted minors prove block rank one for every
specialization of a certificate. -/
theorem certified_blockRankOne (hA : Satisfies roots c A)
    (hP : IntrinsicTests roots realize A P) : BlockRankOne P := by
  intro x y hx hy
  by_cases h : ∃ z, P x z ≠ 0 ∧ P y z ≠ 0
  · obtain ⟨z, hxz, hyz⟩ := h
    exact Or.inl (certified_magnitude_proportional hA hP
      (c.sameRectangle_of_overlap (purified_nonzero_allowed hA hP x z hxz)
        (purified_nonzero_allowed hA hP y z hyz)) hx hy)
  · right
    apply Set.disjoint_left.mpr
    intro z hxz hyz
    exact h ⟨z, hxz, hyz⟩

omit [Fintype D] in
/-- Dependent mode remains dependent after specialization, with all zero
corners handled by the support equations. -/
theorem certified_dependent (hA : Satisfies roots c A)
    (hP : IntrinsicTests roots realize A P) {x y : X}
    (hxy : c.SameRectangle x y) (hx : P x ≠ 0) (hy : P y ≠ 0)
    (hd : (c.pair x y).dependent = true) : RowTypes.Proportional (P x) (P y) := by
  apply (Purification.PurificationMap.proportional_iff_minors hx hy).mpr
  intro z w
  by_cases hz : c.Allowed x z
  · by_cases hw : c.Allowed x w
    · exact (hP.ordinary_minor x y z w).mpr (ordinary_minor hA x y z w hxy hz hw hd)
    · obtain ⟨hxw, hyw⟩ := purified_outside_both hA hP hxy w hw
      simp [hxw, hyw]
  · obtain ⟨hxz, hyz⟩ := purified_outside_both hA hP hxy z hz
    simp [hxz, hyz]

/-- Orthogonal mode remains block-orthogonal when anchors vanish and distinct
certified groups acquire the same magnitude. -/
theorem certified_orthogonal (hA : Satisfies roots c A)
    (hP : IntrinsicTests roots realize A P) (hc : c.Retained roots) {x y : X}
    (hxy : c.SameRectangle x y) (hd : (c.pair x y).dependent = false) :
    VectorBlockOrthogonal (P x) (P y) := by
  classical
  let b : D → Option D := fun z ↦ if c.Allowed x z then some ((c.pair x y).group z) else none
  have hfirst (z : D) (hz : c.Allowed x z) :
      P x z = realize.hom (roots.value ((c.pair x y).firstRoot z)) *
        P x ((c.pair x y).group z) :=
    hP.root_covariance x z _ _ (first_anchor hA x y z hxy hz hd)
  have hsecond (z : D) (hz : c.Allowed x z) :
      P y z = realize.hom (roots.value ((c.pair x y).secondRoot z)) *
        P y ((c.pair x y).group z) :=
    hP.root_covariance y z _ _ (second_anchor hA x y z hxy hz hd)
  apply CertificateAlgebra.vectorBlockOrthogonal_of_fiber_sums (P x) (P y) b
  · intro z w hzw
    by_cases hz : c.Allowed x z
    · by_cases hw : c.Allowed x w
      · have hg : (c.pair x y).group z = (c.pair x y).group w := by
          simpa only [b, if_pos hz, if_pos hw, Option.some.injEq] using hzw
        rw [hfirst z hz, hfirst w hw, norm_mul, norm_mul,
          realize.norm_root, realize.norm_root, one_mul, one_mul, hg]
      · simp only [b, if_pos hz, if_neg hw, reduceCtorEq] at hzw
    · by_cases hw : c.Allowed x w
      · simp only [b, if_neg hz, if_pos hw, reduceCtorEq] at hzw
      · rw [purified_support_zero hA hP x z hz, purified_support_zero hA hP x w hw]
  · intro j
    cases j with
    | none =>
      apply Finset.sum_eq_zero
      intro z hz
      have hz' : ¬ c.Allowed x z := by
        simpa only [b, ite_eq_right_iff, reduceCtorEq, imp_false] using (Finset.mem_filter.mp hz).2
      rw [purified_support_zero hA hP x z hz', zero_mul]
    | some g =>
      have hf : Finset.univ.filter (fun z ↦ b z = some g) =
          (c.columns x).filter (fun z ↦ (c.pair x y).group z = g) := by
        ext z
        by_cases hz : c.Allowed x z <;> simp [b, hz]
      rw [hf]
      apply CertificateAlgebra.hermitianSum_eq_zero_of_anchors (P x) (P y)
        (fun z ↦ realize.hom (roots.value ((c.pair x y).firstRoot z)))
        (fun z ↦ realize.hom (roots.value ((c.pair x y).secondRoot z))) _ (P x g) (P y g)
      · intro z hz
        have hmem := Finset.mem_filter.mp hz
        rw [hfirst z ((c.mem_columns x z).mp hmem.1), hmem.2]
      · intro z hz
        have hmem := Finset.mem_filter.mp hz
        rw [hsecond z ((c.mem_columns x z).mp hmem.1), hmem.2]
      · have hroot := (hc x y hxy hd).2.2.2 g
        have hh := congrArg realize.hom hroot
        simpa only [map_sum, map_mul, map_zero, realize.conj_root] using hh

/-- Soundness of every retained polynomial branch under the intrinsic
purification entry tests. The theorem allows all homogeneous zero degenerations. -/
theorem certificate_sound (hA : Satisfies roots c A)
    (hP : IntrinsicTests roots realize A P) (hc : c.Retained roots) : BlockOrthogonal P := by
  refine ⟨certified_blockRankOne hA hP, ?_⟩
  intro x y hx hy hmag
  have hex : ∃ z, P x z ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  obtain ⟨z, hxz⟩ := hex
  have hyz : P y z ≠ 0 := by
    have hs := magnitudeProportional_support_eq hmag
    change z ∈ support (P y)
    rw [← hs]
    exact hxz
  have hxy : c.SameRectangle x y := c.sameRectangle_of_overlap
    (purified_nonzero_allowed hA hP x z hxz) (purified_nonzero_allowed hA hP y z hyz)
  cases hd : (c.pair x y).dependent with
  | false => exact Or.inr (certified_orthogonal hA hP hc hxy hd)
  | true => exact Or.inl (certified_dependent hA hP hxy hx hy hd)

end ComplexCSP.Certificates
