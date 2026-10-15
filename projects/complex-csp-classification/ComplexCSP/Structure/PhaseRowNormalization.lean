import ComplexCSP.Structure.PhaseNormalizedRows

/-! # Normalizing actual rows into positive magnitudes and finite-order phases -/
noncomputable section
namespace ComplexCSP.PhaseRowNormalization
open scoped BigOperators
open PhasePowerAlgebra BlockOrthogonality RowTypes
variable {D : Type} [Fintype D]

def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem phase_reconstruct (z : ℂ) (hz : z ≠ 0) : (‖z‖ : ℂ)*phase z=z := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  unfold phase
  field_simp

theorem phase_power (z : ℂ) (hz : z ≠ 0) (K : ℕ) (hK : z^K=(‖z‖ : ℂ)^K) :
    phase z^K=1 := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  rw [phase,div_pow,hK,div_self (pow_ne_zero K hn)]

omit [Fintype D] in
/-- The normal form is constructed directly from the actual values and norms.
No supplied row decomposition is needed. -/
theorem normalized_pair (u v : D → ℂ) (hu : ∀ z,u z≠0) (hv : ∀ z,v z≠0)
    (hm : MagnitudeProportional u v) (K : ℕ)
    (hpu : ∀ z,u z^K=(‖u z‖ : ℂ)^K) (hpv : ∀ z,v z^K=(‖v z‖ : ℂ)^K) :
    ∃ b : ℝ, 0<b ∧ ∃ μ : D → ℝ, (∀ z,0<μ z) ∧
      ∃ α β : D → ℂ, (∀ z,α z^K=1) ∧ (∀ z,β z^K=1) ∧
        u=row 1 μ α ∧ v=row b μ β := by
  obtain ⟨c,hc,hm⟩ := hm
  refine ⟨c⁻¹,inv_pos.mpr hc,fun z => ‖u z‖,
    fun z => norm_pos_iff.mpr (hu z),fun z => phase (u z),fun z => phase (v z),
    fun z => phase_power _ (hu z) K (hpu z),fun z => phase_power _ (hv z) K (hpv z),?_,?_⟩
  · funext z
    simpa only [row,Complex.ofReal_one,one_mul] using (phase_reconstruct (u z) (hu z)).symm
  · funext z
    have hn : ‖v z‖ = c⁻¹*‖u z‖ := by rw [hm z]; field_simp
    calc
      v z = (‖v z‖ : ℂ)*phase (v z) := (phase_reconstruct _ (hv z)).symm
      _ = row c⁻¹ (fun z => ‖u z‖) (fun z => phase (v z)) z := by
        rw [hn]
        simp only [row,Complex.ofReal_mul,Complex.ofReal_inv]

/-- The exact four inequalities needed by the magnitude block-rank obstruction. -/
def StrictMinor (u v : D → ℂ) (N : ℕ) : Prop :=
  0 < ‖powerPair u u N‖ ∧ 0 < ‖powerPair u v N‖ ∧ 0 < ‖powerPair v v N‖ ∧
    ‖powerPair u v N‖ * ‖powerPair v u N‖ < ‖powerPair u u N‖ * ‖powerPair v v N‖

theorem bounded_nonzero_rows [Nonempty D] (u v : D → ℂ)
    (hu : ∀ z,u z≠0) (hv : ∀ z,v z≠0) (hm : MagnitudeProportional u v)
    (K : ℕ) (hK : 0<K) (hpu : ∀ z,u z^K=(‖u z‖ : ℂ)^K)
    (hpv : ∀ z,v z^K=(‖v z‖ : ℂ)^K)
    (hind : ¬Proportional u v) (horth : ¬VectorBlockOrthogonal u v) :
    ∃ t : ℕ, 0<t ∧ t ≤ Fintype.card D ∧ StrictMinor u v (t*K) := by
  obtain ⟨b,hb,μ,hμ,α,β,hα,hβ,rfl,rfl⟩ := normalized_pair u v hu hv hm K hpu hpv
  exact PhaseNormalizedRows.bounded_obstruction b hb μ hμ α β K hK hα hβ hind horth

end ComplexCSP.PhaseRowNormalization
