import ComplexCSP.Recognition.CertificatesSoundness

/-!
# Constructing a certificate from Block Orthogonality

The construction uses actual row supports for rectangle labels and canonical
representatives of equal-norm classes for anchor groups. Local root choices
come from the explicit intrinsic entry tests. No certificate or target locus
membership is assumed.
-/

namespace ComplexCSP.Certificates

open scoped BigOperators
open BlockOrthogonality

variable {X D R K : Type*} [Fintype D] [DecidableEq D] [Field K]

noncomputable def actualRowSupport (P : X → D → ℂ) (x : X) : Finset D := by
  classical
  exact Finset.univ.filter (fun z ↦ P x z ≠ 0)

omit [DecidableEq D] in
@[simp] theorem mem_actualRowSupport (P : X → D → ℂ) (x : X) (z : D) :
    z ∈ actualRowSupport P x ↔ P x z ≠ 0 := by
  classical
  simp [actualRowSupport]

noncomputable def actualColumnLabel (P : X → D → ℂ) (z : D) : Finset D := by
  classical
  exact if h : ∃ x, P x z ≠ 0 then actualRowSupport P h.choose else ∅

omit [DecidableEq D] in
theorem actualRowSupport_eq_of_overlap {P : X → D → ℂ} (hP : BlockRankOne P)
    {x y : X} {z : D} (hxz : P x z ≠ 0) (hyz : P y z ≠ 0) :
    actualRowSupport P x = actualRowSupport P y := by
  have hx : P x ≠ 0 := by intro h; exact hxz (congrFun h z)
  have hy : P y ≠ 0 := by intro h; exact hyz (congrFun h z)
  rcases hP x y hx hy with hm | hd
  · have hs := magnitudeProportional_support_eq hm
    ext w
    simpa only [mem_actualRowSupport, support, Set.ext_iff, Set.mem_ofPred_eq] using
      Set.ext_iff.mp hs w
  · exact False.elim (Set.disjoint_left.mp hd hxz hyz)

omit [DecidableEq D] in
theorem actual_labels_allowed_iff {P : X → D → ℂ} (hP : BlockRankOne P)
    (x : X) (z : D) :
    actualRowSupport P x ≠ ∅ ∧ actualRowSupport P x = actualColumnLabel P z ↔ P x z ≠ 0 := by
  classical
  unfold actualColumnLabel
  split_ifs with hex
  · have hw := hex.choose_spec
    constructor
    · intro h
      have hz : z ∈ actualRowSupport P hex.choose := (mem_actualRowSupport _ _ _).mpr hw
      rw [← h.2] at hz
      exact (mem_actualRowSupport _ _ _).mp hz
    · intro hxz
      refine ⟨?_, actualRowSupport_eq_of_overlap hP hxz hw⟩
      intro hempty
      have hmem := (mem_actualRowSupport P x z).mpr hxz
      simp only [hempty, Finset.notMem_empty] at hmem
  · constructor
    · rintro ⟨hn, heq⟩
      exact False.elim (hn heq)
    · intro hxz
      exact False.elim (hex ⟨x, hxz⟩)

/-- The equivalence classes used for certified anchor groups. -/
noncomputable def normSetoid (u : D → ℂ) : Setoid D := Setoid.ker (fun z ↦ ‖u z‖)

noncomputable def normAnchor (u : D → ℂ) (z : D) : D :=
  Quotient.out (Quotient.mk (normSetoid u) z)

omit [Fintype D] [DecidableEq D] in
theorem norm_normAnchor (u : D → ℂ) (z : D) : ‖u (normAnchor u z)‖ = ‖u z‖ :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (normSetoid u) z))

omit [Fintype D] [DecidableEq D] in
theorem normAnchor_eq_of_norm_eq (u : D → ℂ) {z w : D} (h : ‖u z‖ = ‖u w‖) :
    normAnchor u z = normAnchor u w := by
  apply congrArg Quotient.out
  exact Quotient.sound h

omit [Fintype D] [DecidableEq D] in
theorem normAnchor_idempotent (u : D → ℂ) (z : D) :
    normAnchor u (normAnchor u z) = normAnchor u z :=
  normAnchor_eq_of_norm_eq u (norm_normAnchor u z)

omit [Fintype D] [DecidableEq D] in
theorem normAnchor_eq_iff_norm_eq (u : D → ℂ) (z w : D) :
    normAnchor u z = normAnchor u w ↔ ‖u z‖ = ‖u w‖ := by
  constructor
  · intro h
    rw [← norm_normAnchor u z, ← norm_normAnchor u w, h]
  · exact normAnchor_eq_of_norm_eq u

noncomputable def chooseRoot (roots : RootAlphabet K R) (a b : K) : R := by
  classical
  exact if h : ∃ r, a = roots.value r * b then h.choose else roots.one

theorem chooseRoot_spec (roots : RootAlphabet K R) (a b : K)
    (h : ∃ r, a = roots.value r * b) : a = roots.value (chooseRoot roots a b) * b := by
  classical
  simp only [chooseRoot, dif_pos h]
  exact h.choose_spec

noncomputable def chosenPair (roots : RootAlphabet K R) (A : X → D → K)
    (P : X → D → ℂ) (x y : X) : PairData D R := by
  classical
  exact
    { dependent := decide (RowTypes.Proportional (P x) (P y))
      twist := fun z w ↦ chooseRoot roots (A x z * A y w) (A x w * A y z)
      group := normAnchor (P x)
      firstRoot := fun z ↦ chooseRoot roots (A x z) (A x (normAnchor (P x) z))
      secondRoot := fun z ↦ chooseRoot roots (A y z) (A y (normAnchor (P x) z)) }

noncomputable def chosenCertificate (roots : RootAlphabet K R) (A : X → D → K)
    (P : X → D → ℂ) : Certificate X D R where
  rowLabel := actualRowSupport P
  columnLabel := actualColumnLabel P
  pair := chosenPair roots A P

variable {roots : RootAlphabet K R} {realize : ComplexRealization roots}
variable {A : X → D → K} {P : X → D → ℂ}

@[simp] theorem chosenCertificate_allowed_iff (hP : BlockRankOne P) (x : X) (z : D) :
    (chosenCertificate roots A P).Allowed x z ↔ P x z ≠ 0 :=
  actual_labels_allowed_iff hP x z

omit [DecidableEq D] in
private theorem chosen_same_rectangle_rows (hP : BlockRankOne P) {x y : X}
    (hxy : (chosenCertificate roots A P).SameRectangle x y) :
    P x ≠ 0 ∧ P y ≠ 0 ∧ MagnitudeProportional (P x) (P y) := by
  have hne : actualRowSupport P x ≠ ∅ := hxy.1
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hxz : P x z ≠ 0 := (mem_actualRowSupport P x z).mp hz
  have hyz : P y z ≠ 0 := by
    apply (mem_actualRowSupport P y z).mp
    have heq : actualRowSupport P x = actualRowSupport P y := hxy.2
    rw [← heq]
    exact hz
  have hx : P x ≠ 0 := by intro h; exact hxz (congrFun h z)
  have hy : P y ≠ 0 := by intro h; exact hyz (congrFun h z)
  refine ⟨hx, hy, ?_⟩
  rcases hP x y hx hy with hm | hd
  · exact hm
  · exact False.elim (Set.disjoint_left.mp hd hxz hyz)

omit [Fintype D] [DecidableEq D] in
private theorem normAnchor_nonzero (u : D → ℂ) {z : D} (hz : u z ≠ 0) :
    u (normAnchor u z) ≠ 0 := by
  intro hzero
  have hnorm := norm_normAnchor u z
  rw [hzero, norm_zero, eq_comm, norm_eq_zero] at hnorm
  exact hz hnorm

omit [Fintype D] [DecidableEq D] in
private theorem chosen_first_anchor (_hP : BlockRankOne P)
    (tests : IntrinsicTests roots realize A P) (x y : X) (z : D) (hz : P x z ≠ 0) :
    A x z = roots.value ((chosenPair roots A P x y).firstRoot z) *
      A x (normAnchor (P x) z) := by
  apply chooseRoot_spec
  apply (tests.magnitude_anchor x z _ ((tests.zero x _).not.mp (normAnchor_nonzero _ hz))).mp
  exact (norm_normAnchor (P x) z).symm

omit [DecidableEq D] in
private theorem chosen_second_anchor (hP : BlockRankOne P)
    (tests : IntrinsicTests roots realize A P) {x y : X}
    (hxy : (chosenCertificate roots A P).SameRectangle x y) (z : D) (hz : P x z ≠ 0) :
    A y z = roots.value ((chosenPair roots A P x y).secondRoot z) *
      A y (normAnchor (P x) z) := by
  obtain ⟨_, _, hm⟩ := chosen_same_rectangle_rows hP hxy
  have hs := magnitudeProportional_support_eq hm
  have hyg : P y (normAnchor (P x) z) ≠ 0 := by
    change normAnchor (P x) z ∈ support (P y)
    rw [← hs]
    exact normAnchor_nonzero _ hz
  apply chooseRoot_spec
  apply (tests.magnitude_anchor y z _ ((tests.zero y _).not.mp hyg)).mp
  obtain ⟨s, hs, hm⟩ := hm
  apply (mul_right_inj' (ne_of_gt hs)).mp
  rw [← hm z, ← hm _, norm_normAnchor]

/-- The explicitly constructed branch has all its polynomial equations satisfied
by the original table. -/
theorem chosenCertificate_satisfies (hP : BlockOrthogonal P)
    (tests : IntrinsicTests roots realize A P) :
    Satisfies roots (chosenCertificate roots A P) A := by
  classical
  apply (satisfies_iff_equationValues roots _ A).mpr
  intro i
  cases i with
  | support x z =>
    simp only [equationValue]
    split_ifs with h
    · rfl
    · exact (tests.zero x z).mp (by
        by_contra hn
        exact h ((chosenCertificate_allowed_iff hP.1 x z).mpr hn))
  | twisted x y z w =>
    simp only [equationValue]
    split_ifs with h
    · apply sub_eq_zero.mpr
      apply chooseRoot_spec
      obtain ⟨hx, hy, hm⟩ := chosen_same_rectangle_rows hP.1 h.1
      exact (tests.magnitude_minor x y z w).mp
        ((Purification.PurificationMap.magnitudeProportional_iff_minors hx hy).mp hm z w)
    · rfl
  | ordinary x y z w =>
    simp only [equationValue]
    split_ifs with h
    · apply sub_eq_zero.mpr
      apply (tests.ordinary_minor x y z w).mp
      obtain ⟨hx, hy, _⟩ := chosen_same_rectangle_rows hP.1 h.1
      have hd : RowTypes.Proportional (P x) (P y) := by
        have hh := h.2.2.2
        change decide (RowTypes.Proportional (P x) (P y)) = true at hh
        exact of_decide_eq_true hh
      exact (Purification.PurificationMap.proportional_iff_minors hx hy).mp hd z w
    · rfl
  | firstAnchor x y z =>
    simp only [equationValue]
    split_ifs with h
    · apply sub_eq_zero.mpr
      exact chosen_first_anchor hP.1 tests x y z
        ((chosenCertificate_allowed_iff hP.1 x z).mp h.2.1)
    · rfl
  | secondAnchor x y z =>
    simp only [equationValue]
    split_ifs with h
    · apply sub_eq_zero.mpr
      exact chosen_second_anchor hP.1 tests h.1 z
        ((chosenCertificate_allowed_iff hP.1 x z).mp h.2.1)
    · rfl

private theorem chosen_root_sum_zero (hP : BlockOrthogonal P)
    (tests : IntrinsicTests roots realize A P) {x y : X}
    (hxy : (chosenCertificate roots A P).SameRectangle x y)
    (hd : (chosenPair roots A P x y).dependent = false) (g : D) :
    (∑ z ∈ ((chosenCertificate roots A P).columns x).filter
      (fun z ↦ (chosenPair roots A P x y).group z = g),
      roots.value ((chosenPair roots A P x y).firstRoot z) *
      roots.value (roots.conj ((chosenPair roots A P x y).secondRoot z))) = 0 := by
  classical
  let B := ((chosenCertificate roots A P).columns x).filter
    (fun z ↦ (chosenPair roots A P x y).group z = g)
  change (∑ z ∈ B, _) = 0
  by_cases hB : B.Nonempty
  · obtain ⟨w, hw⟩ := hB
    have hwa : (chosenCertificate roots A P).Allowed x w :=
      (Certificate.mem_columns _ x w).mp (Finset.mem_filter.mp hw).1
    have hwp : P x w ≠ 0 := (chosenCertificate_allowed_iff hP.1 x w).mp hwa
    have hwg : normAnchor (P x) w = g := (Finset.mem_filter.mp hw).2
    have hgp : P x g ≠ 0 := hwg ▸ normAnchor_nonzero (P x) hwp
    have hgfix : normAnchor (P x) g = g := by
      rw [← hwg]
      exact normAnchor_idempotent (P x) w
    obtain ⟨hx, hy, hm⟩ := chosen_same_rectangle_rows hP.1 hxy
    have hyg : P y g ≠ 0 := by
      have hs := magnitudeProportional_support_eq hm
      change g ∈ support (P y)
      rw [← hs]
      exact hgp
    have hnormB : B = magnitudeBlock (P x) g := by
      ext z
      dsimp only [B]
      rw [Finset.mem_filter]
      change (z ∈ (chosenCertificate roots A P).columns x ∧ normAnchor (P x) z = g) ↔ _
      rw [Certificate.mem_columns, chosenCertificate_allowed_iff hP.1]
      simp only [magnitudeBlock, Finset.mem_filter, Finset.mem_univ, true_and]
      have hiff := normAnchor_eq_iff_norm_eq (P x) z g
      rw [hgfix] at hiff
      rw [hiff]
      constructor
      · exact And.right
      · intro hn
        refine ⟨?_, hn⟩
        intro hz
        have hgzero : ‖P x g‖ = 0 := by simpa [hz] using hn.symm
        exact hgp (norm_eq_zero.mp hgzero)
    have hnprop : ¬ RowTypes.Proportional (P x) (P y) := by
      change decide (RowTypes.Proportional (P x) (P y)) = false at hd
      exact of_decide_eq_false hd
    have horth := (hP.2 x y hx hy hm).resolve_left hnprop
    have hsumP : hermitianSum (P x) (P y) B = 0 := by
      rw [hnormB]
      exact horth g hgp
    have hfirst (z : D) (hz : z ∈ B) :
        P x z = realize.hom (roots.value ((chosenPair roots A P x y).firstRoot z)) * P x g := by
      have hza := (Certificate.mem_columns _ x z).mp (Finset.mem_filter.mp hz).1
      have hzP := (chosenCertificate_allowed_iff hP.1 x z).mp hza
      have hh := tests.root_covariance x z _ _ (chosen_first_anchor hP.1 tests x y z hzP)
      have hzg : normAnchor (P x) z = g := (Finset.mem_filter.mp hz).2
      simpa only [hzg] using hh
    have hsecond (z : D) (hz : z ∈ B) :
        P y z = realize.hom (roots.value ((chosenPair roots A P x y).secondRoot z)) * P y g := by
      have hza := (Certificate.mem_columns _ x z).mp (Finset.mem_filter.mp hz).1
      have hzP := (chosenCertificate_allowed_iff hP.1 x z).mp hza
      have hh := tests.root_covariance y z _ _ (chosen_second_anchor hP.1 tests hxy z hzP)
      have hzg : normAnchor (P x) z = g := (Finset.mem_filter.mp hz).2
      simpa only [hzg] using hh
    have hf := CertificateAlgebra.hermitianSum_eq_anchor_mul_rootSum (P x) (P y)
      (fun z ↦ realize.hom (roots.value ((chosenPair roots A P x y).firstRoot z)))
      (fun z ↦ realize.hom (roots.value ((chosenPair roots A P x y).secondRoot z)))
      B (P x g) (P y g) hfirst hsecond
    rw [hsumP] at hf
    have hsum := (mul_eq_zero.mp hf.symm).resolve_left
      (mul_ne_zero hgp (by simpa using hyg))
    apply realize.hom.injective
    simpa only [map_sum, map_mul, map_zero, realize.conj_root] using hsum
  · rw [Finset.not_nonempty_iff_eq_empty.mp hB]
    simp

/-- The selected orthogonal groups satisfy every finite retention check. -/
theorem chosenCertificate_retained (hP : BlockOrthogonal P)
    (tests : IntrinsicTests roots realize A P) :
    (chosenCertificate roots A P).Retained roots := by
  intro x y hxy hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    apply (chosenCertificate_allowed_iff hP.1 x _).mpr
    exact normAnchor_nonzero (P x) ((chosenCertificate_allowed_iff hP.1 x z).mp hz)
  · intro z _
    exact normAnchor_idempotent (P x) z
  · intro z hz
    have hzp := (chosenCertificate_allowed_iff hP.1 x z).mp hz
    have hgp := normAnchor_nonzero (P x) hzp
    have hxg : A x (normAnchor (P x) z) ≠ 0 := (tests.zero x _).not.mp hgp
    have hgfix := normAnchor_idempotent (P x) z
    have hfirst := chosen_first_anchor hP.1 tests x y (normAnchor (P x) z) hgp
    rw [hgfix] at hfirst
    have hsecond := chosen_second_anchor hP.1 tests hxy (normAnchor (P x) z) hgp
    rw [hgfix] at hsecond
    obtain ⟨_, _, hm⟩ := chosen_same_rectangle_rows hP.1 hxy
    have hyg : A y (normAnchor (P x) z) ≠ 0 := by
      apply (tests.zero y _).not.mp
      have hs := magnitudeProportional_support_eq hm
      change normAnchor (P x) z ∈ support (P y)
      rw [← hs]
      exact hgp
    constructor
    · apply (mul_left_inj' hxg).mp
      simp only [one_mul]
      exact hfirst.symm
    · apply (mul_left_inj' hyg).mp
      simp only [one_mul]
      exact hsecond.symm
  · intro g
    exact chosen_root_sum_zero hP tests hxy hd g

/-- Completeness: every BO purified table has an actually constructed finite
certificate satisfied by the original table. -/
theorem certificate_complete (hP : BlockOrthogonal P)
    (tests : IntrinsicTests roots realize A P) :
    ∃ c : Certificate X D R, c.Retained roots ∧ Satisfies roots c A :=
  ⟨chosenCertificate roots A P, chosenCertificate_retained hP tests,
    chosenCertificate_satisfies hP tests⟩

/-- The finite algebraic certificate characterization, conditional on the local
intrinsic purification tests. Actual legal-generator construction is a separate
bridge and is not hidden in the statement. -/
theorem blockOrthogonal_iff_certificate
    (tests : IntrinsicTests roots realize A P) :
    BlockOrthogonal P ↔ ∃ c : Certificate X D R, c.Retained roots ∧ Satisfies roots c A := by
  constructor
  · intro hP
    exact certificate_complete hP tests
  · rintro ⟨c, hc, hA⟩
    exact certificate_sound hA tests hc

end ComplexCSP.Certificates
