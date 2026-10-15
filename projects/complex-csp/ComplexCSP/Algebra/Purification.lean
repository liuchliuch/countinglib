import ComplexCSP.Structure.BlockOrthogonality

/-!
# Structural ambient invariance of purification

The map interface isolates the algebraic properties proved from legal generators
in the paper. No existence of legal generators, exponent map, or prime embedding
is asserted here. In particular, Block Orthogonality invariance is a theorem,
not a field of the interface. `Option Γ` represents zero (`none`) and a nonzero
original value (`some x`).
-/

namespace ComplexCSP.Purification

open scoped BigOperators
open BlockOrthogonality RowTypes

universe u v w

/-- The structural output of the generator construction, before denominator
clearing. `original` is the original complex-unit realization of the group. -/
structure PurificationMap (Γ : Type u) [CommGroup Γ] (original : Γ →* ℂˣ) where
  hom : Γ →* ℂˣ
  injective : Function.Injective hom
  fixes_torsion : ∀ x, IsOfFinOrder x → hom x = original x
  norm_one_iff : ∀ x, ‖(hom x : ℂ)‖ = 1 ↔ IsOfFinOrder x

variable {Γ : Type u} [CommGroup Γ] {original : Γ →* ℂˣ}

namespace PurificationMap

noncomputable def value (P : PurificationMap Γ original) (x : Γ) : ℂ := P.hom x

@[simp] theorem value_ne_zero (P : PurificationMap Γ original) (x : Γ) :
    P.value x ≠ 0 := Units.ne_zero _

@[simp] theorem zero_ne_norm_value (P : PurificationMap Γ original) (x : Γ) :
    (0 : ℝ) ≠ ‖P.value x‖ := ne_of_lt (norm_pos_iff.mpr (P.value_ne_zero x))

@[simp] theorem value_mul (P : PurificationMap Γ original) (x y : Γ) :
    P.value (x * y) = P.value x * P.value y := by simp [value]

@[simp] theorem value_div (P : PurificationMap Γ original) (x y : Γ) :
    P.value (x / y) = P.value x / P.value y := by simp [value, map_div]

@[simp] theorem value_eq_iff (P : PurificationMap Γ original) (x y : Γ) :
    P.value x = P.value y ↔ x = y := by
  constructor
  · intro h
    exact P.injective (Units.ext h)
  · exact congrArg _

/-- Equal purified magnitudes are intrinsically torsion ratios. -/
theorem norm_eq_iff_torsion (P : PurificationMap Γ original) (x y : Γ) :
    ‖P.value x‖ = ‖P.value y‖ ↔ IsOfFinOrder (x / y) := by
  rw [← P.norm_one_iff]
  change ‖P.value x‖ = ‖P.value y‖ ↔ ‖P.value (x / y)‖ = 1
  rw [value_div, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr (P.value_ne_zero y))]

/-- The equal-magnitude partition is independent of the ambient purification. -/
theorem norm_eq_iff (P Q : PurificationMap Γ original) (x y : Γ) :
    ‖P.value x‖ = ‖P.value y‖ ↔ ‖Q.value x‖ = ‖Q.value y‖ := by
  rw [P.norm_eq_iff_torsion, Q.norm_eq_iff_torsion]

/-- Multiplicative magnitude minors agree, including all nonzero corners. -/
theorem norm_product_eq_iff (P Q : PurificationMap Γ original) (a b c d : Γ) :
    ‖P.value a * P.value b‖ = ‖P.value c * P.value d‖ ↔
      ‖Q.value a * Q.value b‖ = ‖Q.value c * Q.value d‖ := by
  simpa only [value_mul] using norm_eq_iff P Q (a * b) (c * d)

/-- Ordinary multiplicative minors are reflected by each injective map. -/
theorem product_eq_iff (P : PurificationMap Γ original) (a b c d : Γ) :
    P.value a * P.value b = P.value c * P.value d ↔ a * b = c * d := by
  simpa only [value_mul] using P.value_eq_iff (a * b) (c * d)

/-- Every torsion ratio is preserved pointwise, rather than merely up to norm. -/
theorem torsion_covariance (P : PurificationMap Γ original) (ξ x : Γ)
    (hξ : IsOfFinOrder ξ) : P.value (ξ * x) = (original ξ : ℂ) * P.value x := by
  rw [value_mul]
  change (P.hom ξ : ℂ) * P.value x = _
  rw [P.fixes_torsion ξ hξ]

/-- A common nonzero table scale keeps torsion covariance. -/
theorem scaled_torsion_covariance (P : PurificationMap Γ original) (N : ℂ)
    (ξ x : Γ) (hξ : IsOfFinOrder ξ) :
    N * P.value (ξ * x) = (original ξ : ℂ) * (N * P.value x) := by
  rw [P.torsion_covariance ξ x hξ]
  ring

/-- Entrywise extension which preserves exactly the zero positions. -/
noncomputable def entry (P : PurificationMap Γ original) : Option Γ → ℂ
  | none => 0
  | some x => P.value x

@[simp] theorem entry_none (P : PurificationMap Γ original) : P.entry none = 0 := rfl
@[simp] theorem entry_some (P : PurificationMap Γ original) (x : Γ) :
    P.entry (some x) = P.value x := rfl

@[simp] theorem entry_eq_zero_iff (P : PurificationMap Γ original) (x : Option Γ) :
    P.entry x = 0 ↔ x = none := by
  cases x <;> simp

@[simp] theorem entry_ne_zero_iff (P : PurificationMap Γ original) (x : Option Γ) :
    P.entry x ≠ 0 ↔ x ≠ none := not_congr (P.entry_eq_zero_iff x)

/-- The support of any purified row is precisely its original nonzero positions. -/
theorem support_entry (P : PurificationMap Γ original) {D : Type v} (a : D → Option Γ) :
    support (P.entry ∘ a) = {z | a z ≠ none} := by
  ext z
  simp [support]

/-- Zero rows agree under every purification. -/
theorem row_zero_iff (P Q : PurificationMap Γ original) {D : Type v}
    (a : D → Option Γ) : P.entry ∘ a = 0 ↔ Q.entry ∘ a = 0 := by
  simp only [funext_iff, Function.comp_apply, Pi.zero_apply, entry_eq_zero_iff]

/-- Equal-magnitude tests agree also when either coordinate is zero. -/
theorem entry_norm_eq_iff (P Q : PurificationMap Γ original) (a b : Option Γ) :
    ‖P.entry a‖ = ‖P.entry b‖ ↔ ‖Q.entry a‖ = ‖Q.entry b‖ := by
  cases a with
  | none => cases b <;> simp
  | some a =>
    cases b with
    | none => simp
    | some b => exact P.norm_eq_iff Q a b

/-- Magnitude minor equality is invariant even with zero corners. -/
theorem entry_norm_product_eq_iff (P Q : PurificationMap Γ original)
    (a b c d : Option Γ) :
    ‖P.entry a * P.entry b‖ = ‖P.entry c * P.entry d‖ ↔
      ‖Q.entry a * Q.entry b‖ = ‖Q.entry c * Q.entry d‖ := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    try simp [eq_comm]
  simpa only [norm_mul, eq_comm] using P.norm_product_eq_iff Q _ _ _ _

/-- Complex minor equality is invariant even with zero corners. -/
theorem entry_product_eq_iff (P Q : PurificationMap Γ original)
    (a b c d : Option Γ) :
    P.entry a * P.entry b = P.entry c * P.entry d ↔
      Q.entry a * Q.entry b = Q.entry c * Q.entry d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [product_eq_iff]

/-! ## Row-level consequences of the entry tests -/

private theorem exists_nonzero_coordinate {D : Type v} {u : D → ℂ} (hu : u ≠ 0) :
    ∃ z, u z ≠ 0 := by
  by_contra! h
  exact hu (funext h)

/-- Nonzero row dependence is exactly vanishing of all two-by-two minors. -/
theorem proportional_iff_minors {D : Type v} {u v : D → ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    Proportional u v ↔ ∀ z w, u z * v w = u w * v z := by
  constructor
  · rintro ⟨c, _, h⟩ z w
    rw [h z, h w]
    ring
  · intro h
    obtain ⟨z, hvz⟩ := exists_nonzero_coordinate hv
    obtain ⟨w, huw⟩ := exists_nonzero_coordinate hu
    have huz : u z ≠ 0 := by
      intro hz
      have heq := h w z
      rw [hz, zero_mul] at heq
      exact mul_ne_zero huw hvz heq
    refine ⟨u z / v z, div_ne_zero huz hvz, ?_⟩
    intro i
    apply (mul_left_inj' hvz).mp
    calc
      u i * v z = u z * v i := h i z
      _ = (u z / v z * v i) * v z := by field_simp

/-- Positive magnitude proportionality is likewise characterized by magnitude
minor tests, with positivity following from the nonzero anchor. -/
theorem magnitudeProportional_iff_minors {D : Type v} {u v : D → ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    MagnitudeProportional u v ↔ ∀ z w, ‖u z * v w‖ = ‖u w * v z‖ := by
  constructor
  · rintro ⟨c, _, h⟩ z w
    simp only [norm_mul, h]
    ring
  · intro h
    obtain ⟨z, hvz⟩ := exists_nonzero_coordinate hv
    obtain ⟨w, huw⟩ := exists_nonzero_coordinate hu
    have huz : u z ≠ 0 := by
      intro hz
      have heq := h w z
      rw [hz, zero_mul, norm_zero, norm_eq_zero] at heq
      exact mul_ne_zero huw hvz heq
    refine ⟨‖u z‖ / ‖v z‖, div_pos (norm_pos_iff.mpr huz) (norm_pos_iff.mpr hvz), ?_⟩
    intro i
    apply (mul_left_inj' (norm_ne_zero_iff.mpr hvz)).mp
    calc
      ‖u i‖ * ‖v z‖ = ‖u z‖ * ‖v i‖ := by simpa only [norm_mul] using h i z
      _ = (‖u z‖ / ‖v z‖ * ‖v i‖) * ‖v z‖ := by field_simp

theorem proportional_entry_iff (P Q : PurificationMap Γ original) {D : Type v}
    (a b : D → Option Γ) (ha : P.entry ∘ a ≠ 0) (hb : P.entry ∘ b ≠ 0) :
    Proportional (P.entry ∘ a) (P.entry ∘ b) ↔
      Proportional (Q.entry ∘ a) (Q.entry ∘ b) := by
  have haQ : Q.entry ∘ a ≠ 0 := (not_congr (P.row_zero_iff Q a)).mp ha
  have hbQ : Q.entry ∘ b ≠ 0 := (not_congr (P.row_zero_iff Q b)).mp hb
  rw [proportional_iff_minors ha hb, proportional_iff_minors haQ hbQ]
  exact forall_congr' fun z => forall_congr' fun w =>
    P.entry_product_eq_iff Q (a z) (b w) (a w) (b z)

theorem magnitudeProportional_entry_iff (P Q : PurificationMap Γ original) {D : Type v}
    (a b : D → Option Γ) (ha : P.entry ∘ a ≠ 0) (hb : P.entry ∘ b ≠ 0) :
    MagnitudeProportional (P.entry ∘ a) (P.entry ∘ b) ↔
      MagnitudeProportional (Q.entry ∘ a) (Q.entry ∘ b) := by
  have haQ : Q.entry ∘ a ≠ 0 := (not_congr (P.row_zero_iff Q a)).mp ha
  have hbQ : Q.entry ∘ b ≠ 0 := (not_congr (P.row_zero_iff Q b)).mp hb
  rw [magnitudeProportional_iff_minors ha hb, magnitudeProportional_iff_minors haQ hbQ]
  exact forall_congr' fun z => forall_congr' fun w =>
    P.entry_norm_product_eq_iff Q (a z) (b w) (a w) (b z)

/-- A ratio within one common magnitude block is the same root of unity under
every ambient purification. -/
theorem entry_ratio_eq_of_norm_eq (P Q : PurificationMap Γ original)
    (a b : Option Γ) (h : ‖P.entry a‖ = ‖P.entry b‖) :
    P.entry a / P.entry b = Q.entry a / Q.entry b := by
  cases a with
  | none => simp
  | some a =>
    cases b with
    | none => simp
    | some b =>
      have ht : IsOfFinOrder (a / b) := (P.norm_eq_iff_torsion a b).mp h
      change P.value a / P.value b = Q.value a / Q.value b
      rw [← P.value_div, ← Q.value_div]
      change (P.hom (a / b) : ℂ) = (Q.hom (a / b) : ℂ)
      rw [P.fixes_torsion _ ht, Q.fixes_torsion _ ht]

theorem magnitudeBlock_entry (P Q : PurificationMap Γ original) {D : Type v} [Fintype D]
    (a : D → Option Γ) (z : D) :
    magnitudeBlock (P.entry ∘ a) z = magnitudeBlock (Q.entry ∘ a) z := by
  classical
  ext w
  simp only [magnitudeBlock, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  exact P.entry_norm_eq_iff Q (a w) (a z)

/-- On one magnitude block, changing the purification multiplies all entries
by one common (block-dependent) scalar. -/
theorem entry_rescale_of_norm_eq (P Q : PurificationMap Γ original)
    (a b : Option Γ) (h : ‖P.entry a‖ = ‖P.entry b‖) (hb : Q.entry b ≠ 0) :
    Q.entry a = (Q.entry b / P.entry b) * P.entry a := by
  have hr := P.entry_ratio_eq_of_norm_eq Q a b h
  calc
    Q.entry a = (Q.entry a / Q.entry b) * Q.entry b := (div_mul_cancel₀ _ hb).symm
    _ = (P.entry a / P.entry b) * Q.entry b := by rw [hr]
    _ = (Q.entry b / P.entry b) * P.entry a := by ring

private theorem hermitianSum_rescale_on {D : Type v} (u v u' v' : D → ℂ)
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

/-- Literal Hermitian block vanishing transfers between ambient purifications.
The factorization is proved from torsion covariance on each magnitude block. -/
theorem vectorBlockOrthogonal_transfer (P Q : PurificationMap Γ original)
    {D : Type v} [Fintype D] (a b : D → Option Γ)
    (hmag : MagnitudeProportional (P.entry ∘ a) (P.entry ∘ b))
    (horth : VectorBlockOrthogonal (P.entry ∘ a) (P.entry ∘ b)) :
    VectorBlockOrthogonal (Q.entry ∘ a) (Q.entry ∘ b) := by
  classical
  intro z hzQ
  have hzP : P.entry (a z) ≠ 0 := by
    simpa only [Function.comp_apply, entry_ne_zero_iff] using hzQ
  have hs := magnitudeProportional_support_eq hmag
  have hbzP : P.entry (b z) ≠ 0 := by
    change z ∈ support (P.entry ∘ b)
    rw [← hs]
    exact hzP
  have hbzQ : Q.entry (b z) ≠ 0 := by
    simpa only [entry_ne_zero_iff] using hbzP
  let B := magnitudeBlock (P.entry ∘ a) z
  have hna : ∀ w ∈ B, ‖P.entry (a w)‖ = ‖P.entry (a z)‖ := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  have hnb : ∀ w ∈ B, ‖P.entry (b w)‖ = ‖P.entry (b z)‖ := by
    obtain ⟨c, hc, hmag⟩ := hmag
    intro w hw
    apply (mul_right_inj' (ne_of_gt hc)).mp
    exact (hmag w).symm.trans ((hna w hw).trans (hmag z))
  have haScale : ∀ w ∈ B, (Q.entry ∘ a) w =
      (Q.entry (a z) / P.entry (a z)) * (P.entry ∘ a) w := by
    intro w hw
    exact P.entry_rescale_of_norm_eq Q (a w) (a z) (hna w hw) hzQ
  have hbScale : ∀ w ∈ B, (Q.entry ∘ b) w =
      (Q.entry (b z) / P.entry (b z)) * (P.entry ∘ b) w := by
    intro w hw
    exact P.entry_rescale_of_norm_eq Q (b w) (b z) (hnb w hw) hbzQ
  rw [← P.magnitudeBlock_entry Q a z]
  rw [hermitianSum_rescale_on (P.entry ∘ a) (P.entry ∘ b)
    (Q.entry ∘ a) (Q.entry ∘ b) B _ _ haScale hbScale]
  rw [horth z hzP, mul_zero]

/-- Every clause of literal matrix Block Orthogonality transfers between the
two structural purification maps. No BO statement is a field of the maps. -/
theorem blockOrthogonal_transfer (P Q : PurificationMap Γ original)
    {X : Type v} {D : Type w} [Fintype D] (A : X → D → Option Γ)
    (h : BlockOrthogonal (fun x => P.entry ∘ A x)) :
    BlockOrthogonal (fun x => Q.entry ∘ A x) := by
  constructor
  · intro x y hxQ hyQ
    have hx : P.entry ∘ A x ≠ 0 := (not_congr (P.row_zero_iff Q (A x))).mpr hxQ
    have hy : P.entry ∘ A y ≠ 0 := (not_congr (P.row_zero_iff Q (A y))).mpr hyQ
    rcases h.1 x y hx hy with hmag | hdisj
    · exact Or.inl ((P.magnitudeProportional_entry_iff Q (A x) (A y) hx hy).mp hmag)
    · right
      simpa only [support_entry] using hdisj
  · intro x y hxQ hyQ hmagQ
    have hx : P.entry ∘ A x ≠ 0 := (not_congr (P.row_zero_iff Q (A x))).mpr hxQ
    have hy : P.entry ∘ A y ≠ 0 := (not_congr (P.row_zero_iff Q (A y))).mpr hyQ
    have hmag := (P.magnitudeProportional_entry_iff Q (A x) (A y) hx hy).mpr hmagQ
    rcases h.2 x y hx hy hmag with hdep | horth
    · exact Or.inl ((P.proportional_entry_iff Q (A x) (A y) hx hy).mp hdep)
    · exact Or.inr (P.vectorBlockOrthogonal_transfer Q (A x) (A y) hmag horth)

/-- Lemma 3.1's BO conclusion from the four structural properties of the legal
multiplicative maps. Constructing these maps from legal generators remains a
separate obligation, explicitly absent from this theorem. -/
theorem blockOrthogonal_iff (P Q : PurificationMap Γ original)
    {X : Type v} {D : Type w} [Fintype D] (A : X → D → Option Γ) :
    BlockOrthogonal (fun x => P.entry ∘ A x) ↔
      BlockOrthogonal (fun x => Q.entry ∘ A x) :=
  ⟨P.blockOrthogonal_transfer Q A, Q.blockOrthogonal_transfer P A⟩

/-- Ambient invariance also includes arbitrary positive table-wide denominator
clearing factors, using the independently proved scaling theorem. -/
theorem normalized_blockOrthogonal_iff (P Q : PurificationMap Γ original)
    {X : Type v} {D : Type w} [Fintype D] (A : X → D → Option Γ)
    {N M : ℝ} (hN : 0 < N) (hM : 0 < M) :
    BlockOrthogonal (fun x z => (N : ℂ) * P.entry (A x z)) ↔
      BlockOrthogonal (fun x z => (M : ℂ) * Q.entry (A x z)) := by
  rw [blockOrthogonal_positive_scale_iff hN, blockOrthogonal_positive_scale_iff hM]
  exact P.blockOrthogonal_iff Q A

end PurificationMap
end ComplexCSP.Purification
