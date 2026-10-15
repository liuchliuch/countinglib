import ComplexCSP.Algebra.PowerSums
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Finite relative row phases: algebraic core of Lemma 8.2

The block-orthogonality/purification bridge is not assumed proved here. Its exact
row-level consequence is an explicit hypothesis: each allowed pair of powered
rows is proportional, or its Hermitian sum on a fixed nonempty support block is
zero. From that hypothesis the finite exponent and anchored roots are proved.
-/

namespace ComplexCSP.RowPhases

open scoped BigOperators

/-- Proportionality of two entrywise powers, oriented from `u` to `v`. -/
def PoweredProportional {D K : Type*} [Monoid K] (u v : D → K) (h : ℕ) : Prop :=
  ∃ c : K, ∀ z, v z ^ h = c * u z ^ h

/-- Hermitian sum of powered rows on one block. -/
noncomputable def hermitianBlockPower {D : Type*} (u v : D → ℂ) (B : Finset D) (h : ℕ) : ℂ :=
  ∑ z ∈ B, u z ^ h * star (v z ^ h)

/-- Nonzero entries on a nonempty block make the finite power-sum contradiction
force proportionality for at least one exponent bounded by the row width. -/
theorem exists_poweredProportional {D : Type*} (u v : D → ℂ)
    (B : Finset D) (hB : B.Nonempty)
    (hu : ∀ z ∈ B, u z ≠ 0) (hv : ∀ z ∈ B, v z ≠ 0)
    (d : ℕ) (hcard : B.card ≤ d)
    (hblock : ∀ h, 0 < h → h ≤ d →
      PoweredProportional u v h ∨ hermitianBlockPower u v B h = 0) :
    ∃ h : ℕ, 0 < h ∧ h ≤ d ∧ PoweredProportional u v h := by
  classical
  obtain ⟨b, hb⟩ := hB
  letI : Nonempty B := ⟨⟨b, hb⟩⟩
  obtain ⟨h, hh, hbound, hsum⟩ := ComplexCSP.exists_powerSum_ne_zero_bounded
    (fun z : B ↦ u z * star (v z))
    (fun z ↦ mul_ne_zero (hu z z.property) (by simpa using hv z z.property))
  have hd : h ≤ d := le_trans (by simpa using hbound) hcard
  refine ⟨h, hh, hd, ?_⟩
  rcases hblock h hh hd with hp | hz
  · exact hp
  · exfalso
    apply hsum
    change (∑ z : B, (u z * star (v z)) ^ h) = 0
    rw [Finset.sum_coe_sort B (fun z ↦ (u z * star (v z)) ^ h)]
    simpa only [mul_pow, star_pow, hermitianBlockPower] using hz

/-- The exponent used in the paper: the least common multiple of `1,...,d`. -/
def phaseExponent (d : ℕ) : ℕ := (Finset.Icc 1 d).lcm id

/-- Every possible exponent supplied by the cancellation argument divides the
uniform exponent. -/
theorem dvd_phaseExponent {h d : ℕ} (hh : 0 < h) (hd : h ≤ d) :
    h ∣ phaseExponent d :=
  Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hh, hd⟩)

/-- One common scalar, fixed at the anchor. -/
def anchorScalar {D K : Type*} [DivisionSemiring K] (u v : D → K) (z₀ : D) : K :=
  v z₀ / u z₀

/-- The relative phase is normalized by that single anchor scalar. -/
def anchoredPhase {D K : Type*} [DivisionSemiring K]
    (u v : D → K) (z₀ z : D) : K := (v z / u z) / anchorScalar u v z₀

theorem anchorScalar_ne_zero {D K : Type*} [DivisionSemiring K]
    (u v : D → K) (z₀ : D) (hu : u z₀ ≠ 0) (hv : v z₀ ≠ 0) :
    anchorScalar u v z₀ ≠ 0 := div_ne_zero hv hu

theorem anchoredPhase_anchor {D K : Type*} [DivisionSemiring K]
    (u v : D → K) (z₀ : D) (hu : u z₀ ≠ 0) (hv : v z₀ ≠ 0) :
    anchoredPhase u v z₀ z₀ = 1 := by
  exact div_self (div_ne_zero hv hu)

/-- Reconstruct each row coordinate from the common scalar and relative phase. -/
theorem anchoredPhase_reconstruct {D K : Type*} [Field K]
    (u v : D → K) (z₀ z : D) (hu₀ : u z₀ ≠ 0) (hv₀ : v z₀ ≠ 0)
    (hu : u z ≠ 0) :
    v z = anchorScalar u v z₀ * anchoredPhase u v z₀ z * u z := by
  dsimp [anchorScalar, anchoredPhase]
  field_simp

/-- Proportional powered rows force each anchored phase to be an `h`th root of
unity. This is algebraic; no classification of algebraic roots is needed. -/
theorem anchoredPhase_pow_eq_one {D K : Type*} [Field K]
    (u v : D → K) (z₀ z : D) (hu₀ : u z₀ ≠ 0) (hv₀ : v z₀ ≠ 0)
    (hu : u z ≠ 0) (h : ℕ) (hp : PoweredProportional u v h) :
    anchoredPhase u v z₀ z ^ h = 1 := by
  obtain ⟨c, hc⟩ := hp
  have hc0 : c ≠ 0 := by
    intro hz
    have heq := hc z₀
    rw [hz, zero_mul] at heq
    exact pow_ne_zero h hv₀ heq
  simp only [anchoredPhase, anchorScalar, div_pow, hc]
  simp [hu, hu₀, hc0]

/-- Raising an anchored root to any multiple preserves the value one. -/
theorem anchoredPhase_pow_eq_one_of_dvd {D K : Type*} [Field K]
    (u v : D → K) (z₀ z : D) (hu₀ : u z₀ ≠ 0) (hv₀ : v z₀ ≠ 0)
    (hu : u z ≠ 0) (h L : ℕ) (hp : PoweredProportional u v h) (hL : h ∣ L) :
    anchoredPhase u v z₀ z ^ L = 1 := by
  obtain ⟨k, rfl⟩ := hL
  rw [pow_mul, anchoredPhase_pow_eq_one u v z₀ z hu₀ hv₀ hu h hp, one_pow]

/-- `L_D` is positive, including the empty-lcm case `d = 0`. -/
theorem phaseExponent_pos (d : ℕ) : 0 < phaseExponent d := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro h hh
  exact ne_of_gt (Finset.mem_Icc.mp hh).1

/-- A complete magnitude block, rather than an arbitrary subset of one. -/
noncomputable def magnitudeBlock {D : Type*} [Fintype D]
    (u : D → ℂ) (z₀ : D) : Finset D := by
  classical
  exact Finset.univ.filter (fun z ↦ ‖u z‖ = ‖u z₀‖)

@[simp] theorem mem_magnitudeBlock {D : Type*} [Fintype D]
    (u : D → ℂ) (z₀ z : D) :
    z ∈ magnitudeBlock u z₀ ↔ ‖u z‖ = ‖u z₀‖ := by
  classical
  simp [magnitudeBlock]

/-- Positive powering preserves magnitude blocks exactly. -/
theorem magnitudeBlock_pow {D : Type*} [Fintype D]
    (u : D → ℂ) (z₀ : D) (h : ℕ) (hh : 0 < h) :
    magnitudeBlock (fun z ↦ u z ^ h) z₀ = magnitudeBlock u z₀ := by
  ext z
  simp only [mem_magnitudeBlock, norm_pow]
  exact pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (ne_of_gt hh)

/-- The finite relative-phase conclusion of Lemma 8.2 from the exact finite
row-level orthogonality hypotheses. The hypotheses involving generated tables,
purification, equal supports, and block orthogonality still have to be connected
by the global structural theory; they are not claimed as proved here. -/
theorem finite_relative_row_phases {D : Type*} [Fintype D]
    (u v : D → ℂ) (z₀ : D) (hu₀ : u z₀ ≠ 0) (hv₀ : v z₀ ≠ 0)
    (hsupport : ∀ z, u z = 0 ↔ v z = 0)
    (hblock : ∀ h, 0 < h → h ≤ Fintype.card D →
      PoweredProportional u v h ∨
      hermitianBlockPower u v (magnitudeBlock (fun z ↦ u z ^ h) z₀) h = 0) :
    anchorScalar u v z₀ ≠ 0 ∧ anchoredPhase u v z₀ z₀ = 1 ∧
    ∀ z, u z ≠ 0 →
      v z = anchorScalar u v z₀ * anchoredPhase u v z₀ z * u z ∧
      IsOfFinOrder (anchoredPhase u v z₀ z) ∧
      anchoredPhase u v z₀ z ^ phaseExponent (Fintype.card D) = 1 := by
  classical
  have hB : (magnitudeBlock u z₀).Nonempty :=
    ⟨z₀, (mem_magnitudeBlock u z₀ z₀).mpr rfl⟩
  have huB : ∀ z ∈ magnitudeBlock u z₀, u z ≠ 0 := by
    intro z hz hzero
    have hnorm := (mem_magnitudeBlock u z₀ z).mp hz
    have hn : ‖u z₀‖ = 0 := by simpa [hzero] using hnorm.symm
    exact hu₀ (norm_eq_zero.mp hn)
  have hvB : ∀ z ∈ magnitudeBlock u z₀, v z ≠ 0 := by
    intro z hz hzero
    exact huB z hz ((hsupport z).mpr hzero)
  obtain ⟨h, hh, hd, hp⟩ := exists_poweredProportional u v (magnitudeBlock u z₀)
    hB huB hvB (Fintype.card D) (Finset.card_le_univ _) (by
      intro h hh hd
      simpa only [magnitudeBlock_pow u z₀ h hh] using hblock h hh hd)
  refine ⟨anchorScalar_ne_zero u v z₀ hu₀ hv₀,
    anchoredPhase_anchor u v z₀ hu₀ hv₀, ?_⟩
  intro z hu
  refine ⟨anchoredPhase_reconstruct u v z₀ z hu₀ hv₀ hu, ?_, ?_⟩
  · exact isOfFinOrder_iff_pow_eq_one.mpr
      ⟨h, hh, anchoredPhase_pow_eq_one u v z₀ z hu₀ hv₀ hu h hp⟩
  · exact anchoredPhase_pow_eq_one_of_dvd u v z₀ z hu₀ hv₀ hu h _ hp
      (dvd_phaseExponent hh hd)

end ComplexCSP.RowPhases
