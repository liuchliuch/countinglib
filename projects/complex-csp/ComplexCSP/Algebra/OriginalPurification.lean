import ComplexCSP.Algebra.Purification

/-!
# Purified Block Orthogonality implies original Block Orthogonality

Unlike two legal purifications, an original realization can have extra
magnitude equalities. Its magnitude blocks are therefore coarser. This file
proves the implication using explicit finite fiber sums, not an assumption that
the two block partitions coincide. Legal purification-map existence is still a
separate obligation.
-/
namespace ComplexCSP.Purification.PurificationMap

open BlockOrthogonality RowTypes
open scoped BigOperators

universe u v w
variable {Γ : Type u} [CommGroup Γ] {original : Γ →* ℂˣ}

noncomputable def source (_P : PurificationMap Γ original) : Option Γ → ℂ
  | none => 0
  | some x => original x

@[simp] theorem source_none (P : PurificationMap Γ original) : P.source none = 0 := rfl
@[simp] theorem source_some (P : PurificationMap Γ original) (x : Γ) :
    P.source (some x) = (original x : ℂ) := rfl
@[simp] theorem source_eq_zero_iff (P : PurificationMap Γ original) (a : Option Γ) :
    P.source a = 0 ↔ a = none := by
  cases a <;> simp [Units.ne_zero]
@[simp] theorem source_ne_zero_iff (P : PurificationMap Γ original) (a : Option Γ) :
    P.source a ≠ 0 ↔ a ≠ none := not_congr (P.source_eq_zero_iff a)

theorem source_support (P : PurificationMap Γ original) {D : Type v} (a : D → Option Γ) :
    support (P.source ∘ a) = support (P.entry ∘ a) := by
  ext z
  simp [support]

theorem source_row_zero_iff (P : PurificationMap Γ original) {D : Type v}
    (a : D → Option Γ) : P.source ∘ a = 0 ↔ P.entry ∘ a = 0 := by
  simp only [funext_iff, Function.comp_apply, Pi.zero_apply, source_eq_zero_iff, entry_eq_zero_iff]

theorem source_norm_eq_of (P : PurificationMap Γ original) {a b : Option Γ}
    (h : ‖P.entry a‖ = ‖P.entry b‖) : ‖P.source a‖ = ‖P.source b‖ := by
  cases a with
  | none =>
    have hb : b = none := by
      apply (P.entry_eq_zero_iff b).mp
      exact norm_eq_zero.mp (by simpa only [entry_none, norm_zero] using h.symm)
    simp [hb]
  | some a =>
    cases b with
    | none =>
      have ha : P.value a = 0 := norm_eq_zero.mp (by simpa only [entry_some, entry_none, norm_zero] using h)
      exact False.elim (P.value_ne_zero a ha)
    | some b =>
      have ht := (P.norm_eq_iff_torsion a b).mp h
      have ho := ((Units.coeHom ℂ).comp original).isOfFinOrder ht
      have hn : ‖(original (a / b) : ℂ)‖ = 1 := ho.norm_eq_one
      have hn' : ‖(original a : ℂ)‖ / ‖(original b : ℂ)‖ = 1 := by
        simpa [map_div] using hn
      exact (div_eq_one_iff_eq (norm_ne_zero_iff.mpr (Units.ne_zero _))).mp hn'

theorem source_product_eq_of (P : PurificationMap Γ original) {a b c d : Option Γ}
    (h : P.entry a * P.entry b = P.entry c * P.entry d) :
    P.source a * P.source b = P.source c * P.source d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [entry_none, entry_some, source_none, source_some, zero_mul, mul_zero] at h ⊢ <;>
    try simp_all
  have hg := (P.product_eq_iff _ _ _ _).mp h
  simpa only [map_mul, Units.val_mul] using congrArg (fun x => (original x : ℂ)) hg

theorem source_norm_product_eq_of (P : PurificationMap Γ original) {a b c d : Option Γ}
    (h : ‖P.entry a * P.entry b‖ = ‖P.entry c * P.entry d‖) :
    ‖P.source a * P.source b‖ = ‖P.source c * P.source d‖ := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [entry_none, entry_some, source_none, source_some, zero_mul, mul_zero] at h ⊢ <;>
    try simp_all [eq_comm]
  rename_i a b c d
  have hn := P.source_norm_eq_of (a := some (a * b)) (b := some (c * d))
    (by simpa only [entry_some, value_mul, norm_mul] using h)
  simpa only [source_some, map_mul, Units.val_mul, norm_mul] using hn

theorem source_proportional_of (P : PurificationMap Γ original) {D : Type v}
    (a b : D → Option Γ) (ha : P.entry ∘ a ≠ 0) (hb : P.entry ∘ b ≠ 0)
    (h : Proportional (P.entry ∘ a) (P.entry ∘ b)) :
    Proportional (P.source ∘ a) (P.source ∘ b) := by
  apply (proportional_iff_minors ((not_congr (P.source_row_zero_iff a)).mpr ha)
    ((not_congr (P.source_row_zero_iff b)).mpr hb)).mpr
  intro z w
  exact P.source_product_eq_of ((proportional_iff_minors ha hb).mp h z w)

theorem source_magnitudeProportional_of (P : PurificationMap Γ original) {D : Type v}
    (a b : D → Option Γ) (ha : P.entry ∘ a ≠ 0) (hb : P.entry ∘ b ≠ 0)
    (h : MagnitudeProportional (P.entry ∘ a) (P.entry ∘ b)) :
    MagnitudeProportional (P.source ∘ a) (P.source ∘ b) := by
  apply (magnitudeProportional_iff_minors ((not_congr (P.source_row_zero_iff a)).mpr ha)
    ((not_congr (P.source_row_zero_iff b)).mpr hb)).mpr
  intro z w
  exact P.source_norm_product_eq_of ((magnitudeProportional_iff_minors ha hb).mp h z w)

theorem source_ratio_eq_of_norm_eq (P : PurificationMap Γ original)
    (a b : Option Γ) (h : ‖P.entry a‖ = ‖P.entry b‖) :
    P.entry a / P.entry b = P.source a / P.source b := by
  cases a with
  | none => simp
  | some a =>
    cases b with
    | none => simp
    | some b =>
      have ht := (P.norm_eq_iff_torsion a b).mp h
      change P.value a / P.value b = (original a : ℂ) / (original b : ℂ)
      rw [← P.value_div]
      change (P.hom (a / b) : ℂ) = _
      rw [P.fixes_torsion _ ht]
      simp

theorem source_rescale_of_norm_eq (P : PurificationMap Γ original)
    (a b : Option Γ) (h : ‖P.entry a‖ = ‖P.entry b‖) (hb : P.source b ≠ 0) :
    P.source a = (P.source b / P.entry b) * P.entry a := by
  have hr := P.source_ratio_eq_of_norm_eq a b h
  calc
    P.source a = (P.source a / P.source b) * P.source b := (div_mul_cancel₀ _ hb).symm
    _ = (P.entry a / P.entry b) * P.source b := by rw [hr]
    _ = (P.source b / P.entry b) * P.entry a := by ring

private theorem source_hermitianSum_rescale_on {D : Type v} (u v u' v' : D → ℂ)
    (B : Finset D) (c d : ℂ) (hu : ∀ z ∈ B, u' z = c * u z)
    (hv : ∀ z ∈ B, v' z = d * v z) :
    hermitianSum u' v' B = (c * star d) * hermitianSum u v B := by
  classical
  simp only [hermitianSum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [hu z hz, hv z hz, star_mul]
  ring

/-- Cancellation on a purified magnitude block persists in the original rows. -/
theorem source_sum_on_purified_block (P : PurificationMap Γ original)
    {D : Type v} [Fintype D] (a b : D → Option Γ)
    (hmag : MagnitudeProportional (P.entry ∘ a) (P.entry ∘ b))
    (horth : VectorBlockOrthogonal (P.entry ∘ a) (P.entry ∘ b))
    (z : D) (hzP : P.entry (a z) ≠ 0) :
    hermitianSum (P.source ∘ a) (P.source ∘ b) (magnitudeBlock (P.entry ∘ a) z) = 0 := by
  classical
  have hzO : P.source (a z) ≠ 0 := by simpa only [source_ne_zero_iff, entry_ne_zero_iff] using hzP
  have hs := magnitudeProportional_support_eq hmag
  have hbzP : P.entry (b z) ≠ 0 := by
    change z ∈ support (P.entry ∘ b)
    rw [← hs]
    exact hzP
  have hbzO : P.source (b z) ≠ 0 := by simpa only [source_ne_zero_iff, entry_ne_zero_iff] using hbzP
  let B := magnitudeBlock (P.entry ∘ a) z
  have hna : ∀ w ∈ B, ‖P.entry (a w)‖ = ‖P.entry (a z)‖ := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  have hnb : ∀ w ∈ B, ‖P.entry (b w)‖ = ‖P.entry (b z)‖ := by
    obtain ⟨c, hc, hmag⟩ := hmag
    intro w hw
    apply (mul_right_inj' (ne_of_gt hc)).mp
    exact (hmag w).symm.trans ((hna w hw).trans (hmag z))
  have haScale : ∀ w ∈ B, (P.source ∘ a) w =
      (P.source (a z) / P.entry (a z)) * (P.entry ∘ a) w := by
    intro w hw
    exact P.source_rescale_of_norm_eq (a w) (a z) (hna w hw) hzO
  have hbScale : ∀ w ∈ B, (P.source ∘ b) w =
      (P.source (b z) / P.entry (b z)) * (P.entry ∘ b) w := by
    intro w hw
    exact P.source_rescale_of_norm_eq (b w) (b z) (hnb w hw) hbzO
  rw [source_hermitianSum_rescale_on (P.entry ∘ a) (P.entry ∘ b)
    (P.source ∘ a) (P.source ∘ b) B _ _ haScale hbScale]
  rw [horth z hzP, mul_zero]

/-- The original magnitude partition is a coarsening of the purified one.
Summing the zero contributions of its finer blocks gives original orthogonality. -/
theorem source_vectorBlockOrthogonal (P : PurificationMap Γ original)
    {D : Type v} [Fintype D] (a b : D → Option Γ)
    (hmag : MagnitudeProportional (P.entry ∘ a) (P.entry ∘ b))
    (horth : VectorBlockOrthogonal (P.entry ∘ a) (P.entry ∘ b)) :
    VectorBlockOrthogonal (P.source ∘ a) (P.source ∘ b) := by
  classical
  intro z hz
  let B := magnitudeBlock (P.source ∘ a) z
  let f : D → ℝ := fun w => ‖P.entry (a w)‖
  let g : D → ℂ := fun w => P.source (a w) * star (P.source (b w))
  change (∑ w ∈ B, g w) = 0
  rw [← Finset.sum_fiberwise_of_maps_to (s := B) (t := B.image f)
    (g := f) (fun w hw => Finset.mem_image_of_mem f hw) g]
  apply Finset.sum_eq_zero
  intro r hr
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hr
  have hnormw : ‖P.source (a w)‖ = ‖P.source (a z)‖ := (Finset.mem_filter.mp hw).2
  have hwO : P.source (a w) ≠ 0 := by
    intro hwzero
    have hzNorm : ‖P.source (a z)‖ = 0 := by simpa [hwzero] using hnormw.symm
    exact hz (norm_eq_zero.mp hzNorm)
  have hwP : P.entry (a w) ≠ 0 := by
    simpa only [source_ne_zero_iff, entry_ne_zero_iff] using hwO
  have hfilter : B.filter (fun i => f i = f w) = magnitudeBlock (P.entry ∘ a) w := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, hfi⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfi⟩
    · intro hi
      have hfi := (Finset.mem_filter.mp hi).2
      refine ⟨?_, hfi⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (P.source_norm_eq_of hfi).trans hnormw
  rw [hfilter]
  exact P.source_sum_on_purified_block a b hmag horth w hwP

/-- Block Orthogonality of a structural purification implies BO of the
original complex realization, including coarser original magnitude blocks. -/
theorem source_blockOrthogonal (P : PurificationMap Γ original)
    {X : Type v} {D : Type w} [Fintype D] (A : X → D → Option Γ)
    (h : BlockOrthogonal (fun x => P.entry ∘ A x)) :
    BlockOrthogonal (fun x => P.source ∘ A x) := by
  constructor
  · intro x y hxO hyO
    have hx : P.entry ∘ A x ≠ 0 := (not_congr (P.source_row_zero_iff (A x))).mp hxO
    have hy : P.entry ∘ A y ≠ 0 := (not_congr (P.source_row_zero_iff (A y))).mp hyO
    rcases h.1 x y hx hy with hmag | hd
    · exact Or.inl (P.source_magnitudeProportional_of (A x) (A y) hx hy hmag)
    · right
      simpa only [source_support] using hd
  · intro x y hxO hyO hmagO
    have hx : P.entry ∘ A x ≠ 0 := (not_congr (P.source_row_zero_iff (A x))).mp hxO
    have hy : P.entry ∘ A y ≠ 0 := (not_congr (P.source_row_zero_iff (A y))).mp hyO
    have hmag : MagnitudeProportional (P.entry ∘ A x) (P.entry ∘ A y) := by
      rcases h.1 x y hx hy with hm | hd
      · exact hm
      · exfalso
        have hs := magnitudeProportional_support_eq hmagO
        have hex : ∃ z, (P.source ∘ A x) z ≠ 0 := by
          by_contra! hn
          exact hxO (funext hn)
        obtain ⟨z, hz⟩ := hex
        have hyz : (P.source ∘ A y) z ≠ 0 := by
          change z ∈ support (P.source ∘ A y)
          rw [← hs]
          exact hz
        have hdz : Disjoint (support (P.source ∘ A x)) (support (P.source ∘ A y)) := by
          simpa only [source_support] using hd
        exact Set.disjoint_left.mp hdz hz hyz
    rcases h.2 x y hx hy hmag with hdep | horth
    · exact Or.inl (P.source_proportional_of (A x) (A y) hx hy hdep)
    · exact Or.inr (P.source_vectorBlockOrthogonal (A x) (A y) hmag horth)

/-! ## Canonical encoding of an actual complex table

The option representation is not an extra hypothesis on a table: its intrinsic
multiplicative group and its zero-preserving encoding are constructed below.
-/

/-- The intrinsic group generated by the nonzero entries of a complex table. -/
def entryGroup {X : Type v} {D : Type w} (G : X → D → ℂ) : Subgroup ℂˣ :=
  Subgroup.closure {u | ∃ x z, (u : ℂ) = G x z}

noncomputable def encodeTable {X : Type v} {D : Type w} (G : X → D → ℂ)
    (x : X) (z : D) : Option (entryGroup G) := by
  classical
  exact if h : G x z = 0 then none else
    some ⟨Units.mk0 (G x z) h, Subgroup.subset_closure ⟨x, z, rfl⟩⟩

/-- A concrete purification is the pointwise homomorphic image of the intrinsic
encoding; no existence of the required structural map is asserted. -/
noncomputable def purifyTable {X : Type v} {D : Type w} (G : X → D → ℂ)
    (P : PurificationMap (entryGroup G) (entryGroup G).subtype) : X → D → ℂ :=
  fun x => P.entry ∘ encodeTable G x

@[simp] theorem source_encodeTable {X : Type v} {D : Type w} (G : X → D → ℂ)
    (P : PurificationMap (entryGroup G) (entryGroup G).subtype) (x : X) (z : D) :
    P.source (encodeTable G x z) = G x z := by
  classical
  by_cases h : G x z = 0
  · simp [encodeTable, h]
  · simp [encodeTable, h, source]

/-- The original-table conclusion on actual complex entries, without asking for
an external option-valued representation. -/
theorem original_blockOrthogonal_of_purified {X : Type v} {D : Type w} [Fintype D]
    (G : X → D → ℂ) (P : PurificationMap (entryGroup G) (entryGroup G).subtype)
    (h : BlockOrthogonal (purifyTable G P)) : BlockOrthogonal G := by
  have ho := P.source_blockOrthogonal (encodeTable G) h
  simpa only [Function.comp_def, source_encodeTable] using ho

end ComplexCSP.Purification.PurificationMap
