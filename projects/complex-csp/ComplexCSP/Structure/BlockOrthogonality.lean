import ComplexCSP.Structure.RowTypes

/-!
# The literal complex Block Orthogonality definition

Rows are compared using positive proportionality of their absolute values,
whereas dependence uses nonzero *complex* proportionality. Hermitian sums are
required separately on each positive equal-magnitude block. These notions are
not replaced by a declaration that supports are rectangular.
-/
namespace ComplexCSP
namespace BlockOrthogonality

open MaltsevRelations RowTypes
open scoped BigOperators

universe u v

def support {D : Type u} (u : D → ℂ) : Set D := {z | u z ≠ 0}

def MagnitudeProportional {D : Type u} (u v : D → ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ z, ‖u z‖ = c * ‖v z‖

/-- The entrywise absolute-value matrix has rank one on each support block. -/
def BlockRankOne {X : Type u} {D : Type v} (G : X → D → ℂ) : Prop :=
  ∀ x y, G x ≠ 0 → G y ≠ 0 →
    MagnitudeProportional (G x) (G y) ∨ Disjoint (support (G x)) (support (G y))

noncomputable def magnitudeBlock {D : Type u} [Fintype D]
    (u : D → ℂ) (z : D) : Finset D := by
  classical
  exact Finset.univ.filter fun w => ‖u w‖ = ‖u z‖

noncomputable def hermitianSum {D : Type u} (u v : D → ℂ) (B : Finset D) : ℂ :=
  ∑ z ∈ B, u z * star (v z)

/-- Each nonzero coordinate names its positive equal-magnitude block. Naming a
block several times does not change the condition. -/
def VectorBlockOrthogonal {D : Type u} [Fintype D] (u v : D → ℂ) : Prop :=
  ∀ z, u z ≠ 0 → hermitianSum u v (magnitudeBlock u z) = 0

/-- Definition 2.1, for a matrix of original complex rows. -/
def BlockOrthogonal {X : Type u} {D : Type v} [Fintype D]
    (G : X → D → ℂ) : Prop :=
  BlockRankOne G ∧ ∀ x y, G x ≠ 0 → G y ≠ 0 →
    MagnitudeProportional (G x) (G y) →
      Proportional (G x) (G y) ∨ VectorBlockOrthogonal (G x) (G y)

/-- Literal finite-arity version, with the last coordinate indexing columns. -/
def TableBlockOrthogonal {D : Type u} [Fintype D] {n : ℕ}
    (G : (Fin (n + 1) → D) → ℂ) : Prop := BlockOrthogonal (tableRows G)

theorem magnitudeProportional_support_eq {D : Type u} {u v : D → ℂ}
    (h : MagnitudeProportional u v) : support u = support v := by
  obtain ⟨c, hc, h⟩ := h
  ext z
  have hz : ‖u z‖ = 0 ↔ ‖v z‖ = 0 := by
    rw [h z]
    simp [ne_of_gt hc]
  simpa only [support, Set.mem_ofPred_eq, norm_eq_zero, not_iff_not] using hz

/-- Block-rank one, and hence Block Orthogonality, supplies the support
rectangularity used by the generated-support argument. -/
theorem blockRankOne_support_rectangular {X : Type u} {D : Type v}
    {G : X → D → ℂ} (h : BlockRankOne G) :
    Rectangular (fun x z => G x z ≠ 0) := by
  intro x y a b hxa hya hxb
  have hx : G x ≠ 0 := by intro hz; exact hxa (congrFun hz a)
  have hy : G y ≠ 0 := by intro hz; exact hya (congrFun hz a)
  rcases h x y hx hy with hprop | hdisj
  · have hs := magnitudeProportional_support_eq hprop
    change b ∈ support (G y)
    rw [← hs]
    exact hxb
  · exact False.elim (Set.disjoint_left.mp hdisj hxa hya)

theorem blockOrthogonal_support_rectangular {X : Type u} {D : Type v}
    [Fintype D] {G : X → D → ℂ} (h : BlockOrthogonal G) :
    Rectangular (fun x z => G x z ≠ 0) :=
  blockRankOne_support_rectangular h.1

/-! ## Invariance under a common nonzero complex scale

The paper requires positive real table-wide scaling; the proofs below establish
the slightly stronger nonzero complex statement, and then specialize it.
-/

def scale {D : Type u} (c : ℂ) (u : D → ℂ) : D → ℂ := fun z => c * u z

@[simp] theorem scale_ne_zero_iff {D : Type u} {c : ℂ} (hc : c ≠ 0)
    (u : D → ℂ) : scale c u ≠ 0 ↔ u ≠ 0 := by
  constructor
  · intro h hu
    apply h
    funext z
    change c * u z = 0
    rw [hu]
    simp
  · intro h hu
    apply h
    funext z
    have hz := congrFun hu z
    exact (mul_eq_zero.mp hz).resolve_left hc

@[simp] theorem support_scale {D : Type u} {c : ℂ} (hc : c ≠ 0)
    (u : D → ℂ) : support (scale c u) = support u := by
  ext z
  simp [support, scale, hc]

@[simp] theorem scale_inv_scale {D : Type u} {c : ℂ} (hc : c ≠ 0)
    (u : D → ℂ) : scale c⁻¹ (scale c u) = u := by
  funext z
  simp [scale, hc]

theorem magnitudeProportional_scale {D : Type u} (c : ℂ) {u v : D → ℂ}
    (h : MagnitudeProportional u v) : MagnitudeProportional (scale c u) (scale c v) := by
  obtain ⟨a, ha, h⟩ := h
  refine ⟨a, ha, ?_⟩
  intro z
  simp only [scale, norm_mul, h z]
  ring

theorem magnitudeProportional_scale_iff {D : Type u} {c : ℂ} (hc : c ≠ 0)
    (u v : D → ℂ) :
    MagnitudeProportional (scale c u) (scale c v) ↔ MagnitudeProportional u v := by
  constructor
  · intro h
    simpa only [scale_inv_scale hc] using magnitudeProportional_scale c⁻¹ h
  · exact magnitudeProportional_scale c

theorem proportional_scale {D : Type u} (c : ℂ) {u v : D → ℂ}
    (h : Proportional u v) : Proportional (scale c u) (scale c v) := by
  obtain ⟨a, ha, h⟩ := h
  refine ⟨a, ha, ?_⟩
  intro z
  simp only [scale, h z]
  ring

theorem proportional_scale_iff {D : Type u} {c : ℂ} (hc : c ≠ 0)
    (u v : D → ℂ) : Proportional (scale c u) (scale c v) ↔ Proportional u v := by
  constructor
  · intro h
    simpa only [scale_inv_scale hc] using proportional_scale c⁻¹ h
  · exact proportional_scale c

theorem magnitudeBlock_scale {D : Type u} [Fintype D] {c : ℂ} (hc : c ≠ 0)
    (u : D → ℂ) (z : D) : magnitudeBlock (scale c u) z = magnitudeBlock u z := by
  classical
  ext w
  simp only [magnitudeBlock, Finset.mem_filter, Finset.mem_univ, true_and, scale, norm_mul]
  exact mul_right_inj' (norm_ne_zero_iff.mpr hc)

theorem hermitianSum_scale {D : Type u} (c : ℂ) (u v : D → ℂ) (B : Finset D) :
    hermitianSum (scale c u) (scale c v) B = (c * star c) * hermitianSum u v B := by
  classical
  simp only [hermitianSum, scale, star_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem vectorBlockOrthogonal_scale {D : Type u} [Fintype D]
    {c : ℂ} (hc : c ≠ 0) {u v : D → ℂ} (h : VectorBlockOrthogonal u v) :
    VectorBlockOrthogonal (scale c u) (scale c v) := by
  intro z hz
  rw [magnitudeBlock_scale hc, hermitianSum_scale, h z]
  · simp
  · exact (mul_ne_zero_iff.mp hz).2

theorem vectorBlockOrthogonal_scale_iff {D : Type u} [Fintype D]
    {c : ℂ} (hc : c ≠ 0) (u v : D → ℂ) :
    VectorBlockOrthogonal (scale c u) (scale c v) ↔ VectorBlockOrthogonal u v := by
  constructor
  · intro h
    simpa only [scale_inv_scale hc] using
      vectorBlockOrthogonal_scale (inv_ne_zero hc) h
  · exact vectorBlockOrthogonal_scale hc

theorem blockRankOne_scale_iff {X : Type u} {D : Type v}
    {c : ℂ} (hc : c ≠ 0) (G : X → D → ℂ) :
    BlockRankOne (fun x => scale c (G x)) ↔ BlockRankOne G := by
  simp only [BlockRankOne, scale_ne_zero_iff hc, magnitudeProportional_scale_iff hc,
    support_scale hc]

theorem blockOrthogonal_scale_iff {X : Type u} {D : Type v} [Fintype D]
    {c : ℂ} (hc : c ≠ 0) (G : X → D → ℂ) :
    BlockOrthogonal (fun x => scale c (G x)) ↔ BlockOrthogonal G := by
  simp only [BlockOrthogonal, blockRankOne_scale_iff hc, scale_ne_zero_iff hc,
    magnitudeProportional_scale_iff hc, proportional_scale_iff hc,
    vectorBlockOrthogonal_scale_iff hc]

/-- Positive table-wide normalization, as used when purification denominators
are cleared, changes none of the clauses of Block Orthogonality. -/
theorem blockOrthogonal_positive_scale_iff {X : Type u} {D : Type v} [Fintype D]
    {c : ℝ} (hc : 0 < c) (G : X → D → ℂ) :
    BlockOrthogonal (fun x z => (c : ℂ) * G x z) ↔ BlockOrthogonal G := by
  exact blockOrthogonal_scale_iff (Complex.ofReal_ne_zero.mpr (ne_of_gt hc)) G

end BlockOrthogonality
end ComplexCSP
