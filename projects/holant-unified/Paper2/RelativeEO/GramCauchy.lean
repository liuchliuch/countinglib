import Paper2.Tractable.Scalars
import Mathlib.Tactic

/-! Equality in the finite complex Gram inequality, with an algebraic scalar
recovered from an actual nonzero coordinate. The coefficient field is not
silently enlarged by the Hilbert-space equality theorem. -/
namespace Paper2.RelativeEO
open Tractable
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem complex_proportional_of_gram_equality (u v : ι → ℂ) (B : ℝ)
    (hB : 0 < B) (hu : ∑ i, Complex.normSq (u i) = B)
    (hv : ∑ i, Complex.normSq (v i) = B)
    (hc : Complex.normSq (∑ i, u i * star (v i)) = B ^ 2) :
    ∃ r : ℂ, r ≠ 0 ∧ ∀ i, u i = r * v i := by
  classical
  let C : ℂ := ∑ i, u i * star (v i)
  let r : ℂ := C / (B : ℂ)
  have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hU : (∑ i, u i * star (u i)) = (B : ℂ) := by
    simpa only [Complex.star_def,Complex.mul_conj,← Complex.ofReal_sum] using
      congrArg Complex.ofReal hu
  have hV : (∑ i, v i * star (v i)) = (B : ℂ) := by
    simpa only [Complex.star_def,Complex.mul_conj,← Complex.ofReal_sum] using
      congrArg Complex.ofReal hv
  have hC : C * star C = (B : ℂ) ^ 2 := by
    rw [Complex.star_def,Complex.mul_conj]
    exact_mod_cast hc
  have hC0 : C ≠ 0 := by
    intro hz
    rw [hz,zero_mul] at hC
    exact (pow_ne_zero 2 hB0) hC.symm
  have hrev : (∑ i, v i * star (u i)) = star C := by
    simp only [C,star_sum,star_mul,star_star,mul_comm]
  have hs : (∑ i, (u i - r * v i) * star (u i - r * v i)) = 0 := by
    have hterm (i : ι) : (u i - r * v i) * star (u i - r * v i) =
        u i * star (u i) - star r * (u i * star (v i)) -
          r * (v i * star (u i)) + (r * star r) * (v i * star (v i)) := by
      simp only [star_sub,star_mul]
      ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,
      ← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,hU,hV,hrev]
    change (B : ℂ) - star r * C - r * star C + (r * star r) * (B : ℂ) = 0
    dsimp [r]
    try simp only [star_div,Complex.star_def,Complex.conj_ofReal]
    try rw [Complex.star_def] at hC
    field_simp
    linear_combination -hC
  have hsR : (∑ i, Complex.normSq (u i - r * v i)) = 0 := by
    have he : ((∑ i, Complex.normSq (u i - r * v i)) : ℂ) = 0 := by
      simpa only [Complex.star_def,Complex.mul_conj,← Complex.ofReal_sum] using hs
    exact_mod_cast he
  refine ⟨r,div_ne_zero hC0 hB0,fun i => ?_⟩
  have hz : Complex.normSq (u i - r * v i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).mp hsR i (Finset.mem_univ i)
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hz)

/-- The proportionality scalar can be chosen in the original algebraic field,
not merely in the ambient complex Hilbert space. -/
theorem algebraic_proportional_of_gram_equality (u v : ι → AlgebraicComplex) (B : ℝ)
    (hB : 0 < B) (hu : ∑ i, Complex.normSq (u i : ℂ) = B)
    (hv : ∑ i, Complex.normSq (v i : ℂ) = B)
    (hc : Complex.normSq (∑ i, (u i : ℂ) * star (v i : ℂ)) = B ^ 2) :
    ∃ r : AlgebraicComplex, r ≠ 0 ∧ ∀ i, u i = r * v i := by
  obtain ⟨r, hr, he⟩ := complex_proportional_of_gram_equality
    (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) B hB hu hv hc
  have hex : ∃ j, v j ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : (∑ i, Complex.normSq (v i : ℂ)) = 0 := by simp [h]
    rw [hz] at hv
    linarith
  obtain ⟨j, hj⟩ := hex
  let a : AlgebraicComplex := u j / v j
  have hjC : (v j : ℂ) ≠ 0 := by exact_mod_cast hj
  have har : (a : ℂ) = r := by
    change (u j : ℂ) / (v j : ℂ) = r
    rw [he j, mul_div_cancel_right₀ _ hjC]
  refine ⟨a, ?_, fun i => ?_⟩
  · intro hz
    apply hr
    simpa [hz] using har.symm
  · apply Subtype.ext
    change (u i : ℂ) = (a : ℂ) * (v i : ℂ)
    rw [har]
    exact he i

end
end Paper2.RelativeEO

