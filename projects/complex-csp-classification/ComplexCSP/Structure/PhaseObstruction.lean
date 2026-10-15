import ComplexCSP.Algebra.PowerSums
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Finite phase obstruction algebra

Strict weighted Cauchy–Schwarz and the already proved Vandermonde theorem
provide the finite algebra for Cai–Chen's pure-table phase obstruction.
-/
namespace ComplexCSP.PhaseObstruction
open scoped BigOperators

/-- A positive weighted sum of unit phases reaches its triangle bound only when
all phases agree. Here strictness is derived from the genuine equality case of
Cauchy–Schwarz on finite complex Euclidean space. -/
theorem weighted_phase_strict {D : Type} [Fintype D]
    (w : D → ℝ) (hw : ∀ z, 0 < w z) (δ : D → ℂ) (hδ : ∀ z, ‖δ z‖ = 1)
    (hd : ∃ i j, δ i ≠ δ j) :
    ‖∑ z, (w z : ℂ) * δ z‖ < ∑ z, w z := by
  classical
  obtain ⟨i,j,hij⟩ := hd
  let x : EuclideanSpace ℂ D := WithLp.toLp 2 (fun z => (Real.sqrt (w z) : ℂ))
  let y : EuclideanSpace ℂ D := WithLp.toLp 2 (fun z => (Real.sqrt (w z) : ℂ) * δ z)
  have hx : ‖x‖^2 = ∑ z,w z := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro z _
    simp [x,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hw z).le]
  have hy : ‖y‖^2 = ∑ z,w z := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro z _
    simp [y,hδ,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hw z).le]
  have hnorm : ‖x‖*‖y‖ = ∑ z,w z := by
    have he : ‖x‖ = ‖y‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hx.trans hy.symm)
    rw [←he,←pow_two,hx]
  have hin : inner ℂ x y = ∑ z, (w z : ℂ) * δ z := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro z _
    simp only [RCLike.inner_apply,x,y,PiLp.toLp_apply,
      Complex.conj_ofReal]
    have hs : (Real.sqrt (w z) : ℂ)^2 = (w z : ℂ) := by
      exact_mod_cast Real.sq_sqrt (hw z).le
    calc
      (Real.sqrt (w z) : ℂ) * δ z * (Real.sqrt (w z) : ℂ) =
          (Real.sqrt (w z) : ℂ)^2 * δ z := by ring
      _ = _ := by rw [hs]
  have hsqrt (z : D) : (Real.sqrt (w z) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (hw z))
  have hx0 : x ≠ 0 := by
    intro hz
    have he := congrArg (fun v : EuclideanSpace ℂ D => v i) hz
    exact hsqrt i he
  have hy0 : y ≠ 0 := by
    intro hz
    have he := congrArg (fun v : EuclideanSpace ℂ D => v i) hz
    have hd0 : δ i ≠ 0 := by intro hd0; simpa [hd0] using hδ i
    exact mul_ne_zero (hsqrt i) hd0 he
  have hne : ‖inner ℂ x y‖ ≠ ‖x‖*‖y‖ := by
    intro he
    obtain ⟨c,hc,hcxy⟩ := (norm_inner_eq_norm_iff hx0 hy0).mp he
    have hphase (z : D) : δ z = c := by
      have hz := congrArg (fun v : EuclideanSpace ℂ D => v z) hcxy
      change (Real.sqrt (w z) : ℂ) * δ z = c * (Real.sqrt (w z) : ℂ) at hz
      apply mul_left_cancel₀ (hsqrt z)
      simpa only [mul_comm] using hz
    exact hij ((hphase i).trans (hphase j).symm)
  have hlt := lt_of_le_of_ne (norm_inner_le_norm x y) hne
  simpa only [hin,hnorm] using hlt

/-- Finite grouped positive bases turn a nonzero block phase sum into a
nonzero positive moment among the first number-of-blocks moments. -/
theorem block_moment_nonzero {D I : Type} [Fintype D] [Fintype I] [DecidableEq I]
    (block : D → I) (b : I → ℝ) (hb : ∀ i, 0 < b i)
    (hinj : Function.Injective b) (δ : D → ℂ)
    (hblock : ∃ i, (∑ z ∈ Finset.univ.filter (fun z => block z = i), δ z) ≠ 0) :
    ∃ t : ℕ, 0 < t ∧ t ≤ Fintype.card I ∧
      (∑ z, (b (block z) : ℂ)^t * δ z) ≠ 0 := by
  classical
  let c := fun i => ∑ z ∈ Finset.univ.filter (fun z => block z = i), δ z
  have hbase : Function.Injective (fun i => (b i : ℂ)) :=
    Complex.ofReal_injective.comp hinj
  have hb0 (i : I) : (b i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hb i)
  obtain ⟨i,hi⟩ := hblock
  obtain ⟨k,hk,hne⟩ := exists_weightedPowerSum_ne_zero_fintype
    (fun j => c j * (b j : ℂ)) (fun j => (b j : ℂ)) hbase
    ⟨i,mul_ne_zero hi (hb0 i)⟩
  refine ⟨k+1,by omega,by omega,?_⟩
  have he : weightedPowerSum (fun j => c j * (b j : ℂ)) (fun j => (b j : ℂ)) k =
      ∑ z, (b (block z) : ℂ)^(k+1) * δ z := by
    unfold weightedPowerSum
    calc
      _ = ∑ j, ∑ z ∈ Finset.univ.filter (fun z => block z = j),
          (b (block z) : ℂ)^(k+1) * δ z := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [c,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro z hz
        rw [(Finset.mem_filter.mp hz).2]
        ring
      _ = _ := Finset.sum_fiberwise Finset.univ block _
  rwa [he] at hne

/-- Bounded phase witness with both inequalities needed by the strict 2×2
magnitude determinant. No eventual-zero theorem or analytic limit is used. -/
theorem bounded_phase_obstruction {D I : Type} [Fintype D] [Fintype I] [DecidableEq I]
    (block : D → I) (b : I → ℝ) (hb : ∀ i, 0 < b i)
    (hinj : Function.Injective b) (δ : D → ℂ) (hδ : ∀ z, ‖δ z‖ = 1)
    (hd : ∃ i j, δ i ≠ δ j)
    (hblock : ∃ i, (∑ z ∈ Finset.univ.filter (fun z => block z = i), δ z) ≠ 0) :
    ∃ t : ℕ, 0 < t ∧ t ≤ Fintype.card I ∧
      0 < ‖∑ z, (b (block z) : ℂ)^t * δ z‖ ∧
      ‖∑ z, (b (block z) : ℂ)^t * δ z‖ < ∑ z, b (block z)^t := by
  obtain ⟨t,ht,hbound,hne⟩ := block_moment_nonzero block b hb hinj δ hblock
  refine ⟨t,ht,hbound,norm_pos_iff.mpr hne,?_⟩
  simpa only [Complex.ofReal_pow] using
    weighted_phase_strict (fun z => b (block z)^t)
      (fun z => pow_pos (hb _) _) δ hδ hd

end ComplexCSP.PhaseObstruction
