import Paper2.RelativeEO.ARSFactors

/-! A nonzero fixed-central-weight tensor has a pair with unequal 00 and 01
squared slice masses. This finite variance identity is independent of ARS,
positivity normalization, or any counting-complexity assumption. -/
namespace Paper2.RelativeEO
open scoped BigOperators

private def spin (b : Bool) : ℝ := if b then -1 else 1

private theorem spin_sum {n : ℕ} (x : Fin n → Bool) :
    (∑ j, spin (x j)) = (n : ℝ) - 2 * (weight x : ℝ) := by
  have hh (b : Bool) : spin b = 1 - 2 * (if b then (1 : ℝ) else 0) := by
    cases b <;> norm_num [spin]
  simp_rw [hh]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]
  simp [weight,Nat.cast_sum]

/-- Full-table squared mass of a fixed ordered two-port pattern. -/
noncomputable def pairMass {n : ℕ} (f : Signature ℂ n) (i j : Fin n) (a b : Bool) : ℝ :=
  ∑ x : Fin n → Bool, if x i = a ∧ x j = b then Complex.normSq (f x) else 0

private noncomputable def rowCorrelation {n : ℕ} (f : Signature ℂ n) (i j : Fin n) : ℝ :=
  ∑ x : Fin n → Bool, if x i then 0 else Complex.normSq (f x) * spin (x j)

private theorem rowCorrelation_mass {n : ℕ} (f : Signature ℂ n) (i j : Fin n) :
    rowCorrelation f i j = pairMass f i j false false - pairMass f i j false true := by
  rw [rowCorrelation,pairMass,pairMass,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  cases hi : x i <;> cases hj : x j <;> simp [hi,hj,spin]

private theorem rowCorrelation_sum_zero {n : ℕ} (f : Signature ℂ n)
    (he : Signature.CentralSupport f) (i : Fin n) : (∑ j, rowCorrelation f i j) = 0 := by
  unfold rowCorrelation
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x _
  cases hi : x i
  · simp only [hi,Bool.false_eq_true,↓reduceIte,← Finset.mul_sum]
    by_cases hz : f x = 0
    · simp [hz]
    · have hw : 2 * weight x = n := by by_contra hh; exact hz (he x hh)
      rw [spin_sum]
      have hwR : (2 : ℝ) * (weight x : ℝ) = (n : ℝ) := by exact_mod_cast hw
      rw [hwR,sub_self,mul_zero]
  · simp [hi]

/-- Every positive-arity nonzero EO tensor has a genuine two-port marginal
which is not uniform across the two values of its second bit. -/
theorem exists_unequal_pair_mass {n : ℕ} (f : Signature ℂ n)
    (hn : 0 < n) (hf : f ≠ 0) (he : Signature.CentralSupport f) :
    ∃ i j : Fin n, i ≠ j ∧ pairMass f i j false false ≠ pairMass f i j false true := by
  classical
  obtain ⟨x,hx⟩ : ∃ x, f x ≠ 0 := by by_contra h; push Not at h; exact hf (funext h)
  have hxw : 2 * weight x = n := by by_contra hh; exact hx (he x hh)
  obtain ⟨i,hi⟩ : ∃ i : Fin n, x i = false := by
    by_contra hh
    push Not at hh
    have hxall : x = fun _ => true := by
      funext j
      cases hj : x j
      · exact False.elim (hh j hj)
      · rfl
    have hw : weight x = n := by simp [hxall,weight]
    omega
  have hdiag : 0 < rowCorrelation f i i := by
    unfold rowCorrelation
    apply Finset.sum_pos'
    · intro y _
      cases hy : y i <;> simp [hy,spin,Complex.normSq_nonneg]
    · refine ⟨x,Finset.mem_univ _,?_⟩
      simp only [hi,Bool.false_eq_true,↓reduceIte,spin,mul_one]
      exact Complex.normSq_pos.mpr hx
  by_contra hh
  push Not at hh
  have hzero (j : Fin n) (hji : j ≠ i) : rowCorrelation f i j = 0 := by
    rw [rowCorrelation_mass,hh i j (Ne.symm hji),sub_self]
  have hsum : (∑ j, rowCorrelation f i j) = rowCorrelation f i i := by
    apply Finset.sum_eq_single i
    · intro j _ hj
      exact hzero j hj
    · simp
  have hz := rowCorrelation_sum_zero f he i
  rw [hsum] at hz
  linarith

end Paper2.RelativeEO
