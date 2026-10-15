import ComplexCSP.Algebra.GaussianRational
import Mathlib.Topology.MetricSpace.Contracting

/-! # Finite-power estimates for rational complex root certificates -/

namespace ComplexCSP.ComplexRootCertificates

open scoped BigOperators

/-- The elementary finite-power Lipschitz estimate on a complex disk. -/
theorem norm_pow_sub_pow_le (z w : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) (n : ℕ) :
    ‖z^(n+1) - w^(n+1)‖ ≤ ((n+1 : ℕ) : ℝ) * r^n * ‖z-w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hid : z^(n+1+1)-w^(n+1+1) =
        z * (z^(n+1)-w^(n+1)) + (z-w)*w^(n+1) := by ring
    rw [hid]
    calc
      _ ≤ ‖z * (z^(n+1)-w^(n+1))‖ + ‖(z-w)*w^(n+1)‖ := norm_add_le _ _
      _ = ‖z‖ * ‖z^(n+1)-w^(n+1)‖ + ‖z-w‖ * ‖w‖^(n+1) := by
        rw [norm_mul, norm_mul, norm_pow]
      _ ≤ r * (((n+1 : ℕ) : ℝ) * r^n * ‖z-w‖) + ‖z-w‖ * r^(n+1) := by
        gcongr
      _ = _ := by push_cast; ring

noncomputable def tailEval {n : ℕ} (a : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ j, a j * z^(j.val+2)

noncomputable def tailBound {n : ℕ} (a : Fin n → ℂ) (r : ℝ) : ℝ :=
  ∑ j, ((j.val+2 : ℕ) : ℝ) * ‖a j‖ * r^(j.val+1)

@[simp] theorem tailEval_zero {n : ℕ} (a : Fin n → ℂ) : tailEval a 0 = 0 := by
  simp [tailEval]

theorem tailBound_nonneg {n : ℕ} (a : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ tailBound a r := by
  apply Finset.sum_nonneg
  intro j _
  positivity

theorem tailEval_lipschitz {n : ℕ} (a : Fin n → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (z w : ℂ) (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖tailEval a z - tailEval a w‖ ≤ tailBound a r * ‖z-w‖ := by
  rw [tailEval, tailEval, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, ‖a j * z^(j.val+2) - a j * w^(j.val+2)‖ := norm_sum_le _ _
    _ = ∑ j, ‖a j‖ * ‖z^(j.val+2)-w^(j.val+2)‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_sub, norm_mul]
    _ ≤ ∑ j, ‖a j‖ * (((j.val+2 : ℕ) : ℝ)*r^(j.val+1)*‖z-w‖) := by
      apply Finset.sum_le_sum
      intro j _
      gcongr
      exact norm_pow_sub_pow_le z w r hr hz hw (j.val+1)
    _ = tailBound a r * ‖z-w‖ := by
      rw [tailBound, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem tailEval_norm_le {n : ℕ} (a : Fin n → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (z : ℂ) (hz : ‖z‖ ≤ r) : ‖tailEval a z‖ ≤ tailBound a r * ‖z‖ := by
  simpa using tailEval_lipschitz a r hr z 0 hz (by simpa using hr)

/-- Banach's theorem applied to the explicitly controlled Taylor remainder.
No root, approximate-root convergence, or uniqueness premise is supplied. -/
theorem unique_root_of_bounds {n : ℕ} (t₀ t₁ : ℂ) (a : Fin n → ℂ)
    (r L B : ℝ) (hr : 0 < r) (hL : 0 < L) (hLnorm : L ≤ ‖t₁‖)
    (hB : tailBound a r ≤ B) (hBL : B < L)
    (hsmall : ‖t₀‖ + B*r < L*r) :
    ∃! z : ℂ, ‖z‖ ≤ r ∧ t₀ + t₁*z + tailEval a z = 0 := by
  have ht₁ : t₁ ≠ 0 := norm_pos_iff.mp (hL.trans_le hLnorm)
  have hn : 0 < ‖t₁‖ := norm_pos_iff.mpr ht₁
  have hB0 : 0 ≤ B := (tailBound_nonneg a hr.le).trans hB
  let K : NNReal := ⟨B / ‖t₁‖, div_nonneg hB0 hn.le⟩
  have hK : K < 1 := (div_lt_one hn).mpr (hBL.trans_le hLnorm)
  let F : ℂ → ℂ := fun z ↦ -(t₀ + tailEval a z) / t₁
  have hmaps : Set.MapsTo F (Metric.closedBall 0 r) (Metric.closedBall 0 r) := by
    intro z hz
    have hz' : ‖z‖ ≤ r := by simpa using hz
    change dist (F z) 0 ≤ r
    rw [dist_zero_right]
    dsimp [F]
    rw [norm_div, norm_neg]
    apply (div_le_iff₀ hn).mpr
    calc
      ‖t₀ + tailEval a z‖ ≤ ‖t₀‖ + ‖tailEval a z‖ := norm_add_le _ _
      _ ≤ ‖t₀‖ + B*r := by
        gcongr
        exact (tailEval_norm_le a r hr.le z hz').trans
          (mul_le_mul hB hz' (norm_nonneg _) hB0)
      _ ≤ r * ‖t₁‖ := hsmall.le.trans (by nlinarith)
  have hcontract : ContractingWith K (hmaps.restrict F _ _) := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul ?_⟩
    intro z w
    simp only [Subtype.dist_eq, dist_eq_norm]
    change ‖F z - F w‖ ≤ (B / ‖t₁‖) * ‖(z:ℂ)-w‖
    have hze : ‖(z:ℂ)‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
    have hwe : ‖(w:ℂ)‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using w.property
    have hid : F z - F w = -(tailEval a z - tailEval a w) / t₁ := by dsimp [F]; ring
    rw [hid, norm_div, norm_neg]
    calc
      _ ≤ (B * ‖(z:ℂ)-w‖) / ‖t₁‖ := by
        apply div_le_div_of_nonneg_right _ hn.le
        exact (tailEval_lipschitz a r hr.le z w hze hwe).trans
          (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
      _ = _ := by ring
  obtain ⟨z,hz,hfix,_,_⟩ := hcontract.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hmaps (by simpa using hr.le : (0:ℂ) ∈ Metric.closedBall 0 r)
    (edist_ne_top _ _)
  have hfixed_iff (w : ℂ) : F w = w ↔ t₀ + t₁*w + tailEval a w = 0 := by
    dsimp [F]
    rw [div_eq_iff ht₁]
    constructor <;> intro h <;> linear_combination -h
  refine ⟨z, ⟨by simpa using hz, (hfixed_iff z).mp hfix⟩, ?_⟩
  intro w hw
  have hwball : w ∈ Metric.closedBall (0:ℂ) r := by simpa using hw.1
  have hsub : (⟨w,hwball⟩ : Metric.closedBall (0:ℂ) r) = ⟨z,hz⟩ :=
    hcontract.fixedPoint_unique' (Subtype.ext ((hfixed_iff w).mpr hw.2)) (Subtype.ext hfix)
  exact congrArg Subtype.val hsub

end ComplexCSP.ComplexRootCertificates
