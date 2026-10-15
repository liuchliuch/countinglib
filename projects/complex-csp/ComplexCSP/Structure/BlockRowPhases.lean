import ComplexCSP.Structure.BlockOrthogonality
import ComplexCSP.Structure.RowPhases

/-!
# Block Orthogonality supplies the finite relative-phase hypotheses

This connects the literal complex-table BO definition to the finite power-sum
argument, removing the latter's abstract row-level disjunction. The remaining
global input is BO for the original generated positive powers; deriving it from
legal purification is a separate mathematical obligation.
-/
namespace ComplexCSP.BlockOrthogonality

open MaltsevRelations RowTypes

universe u v

theorem magnitudeProportional_of_overlap {X : Type u} {D : Type v}
    {G : X → D → ℂ} (hG : BlockRankOne G) (x y : X) (z : D)
    (hxz : G x z ≠ 0) (hyz : G y z ≠ 0) : MagnitudeProportional (G x) (G y) := by
  have hx : G x ≠ 0 := by intro hz; exact hxz (congrFun hz z)
  have hy : G y ≠ 0 := by intro hz; exact hyz (congrFun hz z)
  rcases hG x y hx hy with hp | hd
  · exact hp
  · exact False.elim (Set.disjoint_left.mp hd hxz hyz)

theorem magnitudeProportional_pow {D : Type u} {u v : D → ℂ}
    (h : MagnitudeProportional u v) (n : ℕ) :
    MagnitudeProportional (fun z => u z ^ n) (fun z => v z ^ n) := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c ^ n, pow_pos hc n, fun z => by simp only [norm_pow, h z, mul_pow]⟩

/-- The powered proportionality/vanishing alternative is a consequence of the
actual BO definition, not an additional row-level assumption. -/
theorem power_row_alternative {X : Type u} {D : Type v} [Fintype D]
    (G : X → D → ℂ) (n : ℕ) (hG : BlockOrthogonal (fun x z => G x z ^ n))
    (x y : X) (z₀ : D) (hxz : G x z₀ ≠ 0) (hyz : G y z₀ ≠ 0) :
    RowPhases.PoweredProportional (G x) (G y) n ∨
      RowPhases.hermitianBlockPower (G x) (G y)
        (RowPhases.magnitudeBlock (fun z => G x z ^ n) z₀) n = 0 := by
  have hxpow : G x z₀ ^ n ≠ 0 := pow_ne_zero n hxz
  have hypow : G y z₀ ^ n ≠ 0 := pow_ne_zero n hyz
  have hx : (fun z => G x z ^ n) ≠ 0 := by intro hz; exact hxpow (congrFun hz z₀)
  have hy : (fun z => G y z ^ n) ≠ 0 := by intro hz; exact hypow (congrFun hz z₀)
  have hmag := magnitudeProportional_of_overlap hG.1 x y z₀ hxpow hypow
  rcases hG.2 x y hx hy hmag with hp | hb
  · obtain ⟨c, _, hc⟩ := proportional_symm hp
    exact Or.inl ⟨c, hc⟩
  · exact Or.inr (hb z₀ hxpow)

/-- Full finite relative row phases from BO of the first `|D|` entrywise powers.
The support equality is proved here as well. -/
theorem finite_row_phases_of_power_BO {X : Type u} {D : Type v} [Fintype D]
    (G : X → D → ℂ)
    (hG : ∀ h, 0 < h → h ≤ Fintype.card D →
      BlockOrthogonal (fun x z => G x z ^ h))
    (x y : X) (z₀ : D) (hxz : G x z₀ ≠ 0) (hyz : G y z₀ ≠ 0) :
    support (G x) = support (G y) ∧
    RowPhases.anchorScalar (G x) (G y) z₀ ≠ 0 ∧
    RowPhases.anchoredPhase (G x) (G y) z₀ z₀ = 1 ∧
    ∀ z, G x z ≠ 0 →
      G y z = RowPhases.anchorScalar (G x) (G y) z₀ *
        RowPhases.anchoredPhase (G x) (G y) z₀ z * G x z ∧
      IsOfFinOrder (RowPhases.anchoredPhase (G x) (G y) z₀ z) ∧
      RowPhases.anchoredPhase (G x) (G y) z₀ z ^
        RowPhases.phaseExponent (Fintype.card D) = 1 := by
  have hcard : 1 ≤ Fintype.card D := Fintype.card_pos_iff.mpr ⟨z₀⟩
  have hG₁ : BlockOrthogonal G := by simpa only [pow_one] using hG 1 (by omega) hcard
  have hsupport := magnitudeProportional_support_eq
    (magnitudeProportional_of_overlap hG₁.1 x y z₀ hxz hyz)
  refine ⟨hsupport, ?_⟩
  apply RowPhases.finite_relative_row_phases (G x) (G y) z₀ hxz hyz
  · intro z
    have hz : (G x z ≠ 0) ↔ (G y z ≠ 0) := Set.ext_iff.mp hsupport z
    exact not_iff_not.mp hz
  · intro h hh hd
    exact power_row_alternative G h (hG h hh hd) x y z₀ hxz hyz

end ComplexCSP.BlockOrthogonality
