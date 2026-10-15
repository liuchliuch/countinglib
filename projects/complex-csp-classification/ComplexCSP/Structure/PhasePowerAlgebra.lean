import ComplexCSP.Structure.PhaseObstruction

/-! # Literal two-power entries of normalized pure rows -/
noncomputable section
namespace ComplexCSP.PhasePowerAlgebra
open scoped BigOperators
variable {D : Type} [Fintype D]

def row (a : ℝ) (μ : D → ℝ) (α : D → ℂ) (z : D) : ℂ := (a : ℂ) * μ z * α z

def powerPair (u v : D → ℂ) (N : ℕ) : ℂ := ∑ z, u z * v z^(N-1)

theorem phase_pow_pred {z : ℂ} {N : ℕ} (hN : 0<N) (hz : z^N=1) :
    z^(N-1) = star z := by
  have hn := Complex.norm_eq_one_of_pow_eq_one hz (ne_of_gt hN)
  have hz0 : z ≠ 0 := by intro he; simp [he,ne_of_gt hN] at hz
  apply mul_right_cancel₀ hz0
  rw [pow_sub_one_mul (ne_of_gt hN),hz,mul_comm]
  change 1 = z * (starRingEnd ℂ) z
  rw [Complex.mul_conj',hn]
  norm_num

/-- This is the exact finite algebra of the off-diagonal edge entry. -/
theorem powerPair_normal_form (a b : ℝ) (μ : D → ℝ) (α β : D → ℂ)
    (N : ℕ) (hN : 0<N) (hβ : ∀ z, β z^N=1) :
    powerPair (row a μ α) (row b μ β) N =
      (a : ℂ)*(b : ℂ)^(N-1) * ∑ z, (μ z : ℂ)^N * (α z * star (β z)) := by
  rw [powerPair,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [row,mul_pow,phase_pow_pred hN (hβ z)]
  rw [←pow_sub_one_mul (ne_of_gt hN) (μ z : ℂ)]
  ring

theorem powerPair_diagonal (a : ℝ) (μ : D → ℝ) (α : D → ℂ)
    (N : ℕ) (hN : 0<N) (hα : ∀ z, α z^N=1) :
    powerPair (row a μ α) (row a μ α) N = (a : ℂ)^N * ∑ z, (μ z : ℂ)^N := by
  rw [powerPair_normal_form a a μ α α N hN hα]
  have hn (z : D) : α z * star (α z) = 1 := by
    change α z * (starRingEnd ℂ) (α z) = 1
    rw [Complex.mul_conj',Complex.norm_eq_one_of_pow_eq_one (hα z) (ne_of_gt hN)]
    norm_num
  simp only [hn,mul_one]
  rw [mul_comm (a : ℂ),pow_sub_one_mul (ne_of_gt hN)]

/-- Strict phase triangle inequality becomes a strict principal magnitude
minor after restoring both positive row scales. -/
theorem strict_minor_of_phase_sum (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (μ : D → ℝ) (α β : D → ℂ)
    (N : ℕ) (hN : 0<N) (hα : ∀ z, α z^N=1) (hβ : ∀ z, β z^N=1)
    (hL : 0 < ‖∑ z, (μ z : ℂ)^N * (α z * star (β z))‖)
    (hlt : ‖∑ z, (μ z : ℂ)^N * (α z * star (β z))‖ < ∑ z, μ z^N) :
    0 < ‖powerPair (row a μ α) (row a μ α) N‖ ∧
    0 < ‖powerPair (row a μ α) (row b μ β) N‖ ∧
    0 < ‖powerPair (row b μ β) (row b μ β) N‖ ∧
    ‖powerPair (row a μ α) (row b μ β) N‖ *
        ‖powerPair (row b μ β) (row a μ α) N‖ <
      ‖powerPair (row a μ α) (row a μ α) N‖ *
        ‖powerPair (row b μ β) (row b μ β) N‖ := by
  let S : ℝ := ∑ z,μ z^N
  let L : ℂ := ∑ z,(μ z : ℂ)^N * (α z * star (β z))
  have hS : 0<S := hL.trans hlt
  have hreal : (∑ z,(μ z : ℂ)^N) = (S : ℂ) := by simp [S]
  have hconj : (∑ z,(μ z : ℂ)^N * (β z * star (α z))) = star L := by
    simp only [L,star_sum,star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]
    simp only [starRingEnd_self_apply]
    apply Finset.sum_congr rfl
    intro z _
    ring
  have haa : ‖powerPair (row a μ α) (row a μ α) N‖ = a^N*S := by
    rw [powerPair_diagonal a μ α N hN hα,hreal]
    simp [abs_of_nonneg ha.le,abs_of_nonneg hS.le]
  have hbb : ‖powerPair (row b μ β) (row b μ β) N‖ = b^N*S := by
    rw [powerPair_diagonal b μ β N hN hβ,hreal]
    simp [abs_of_nonneg hb.le,abs_of_nonneg hS.le]
  have hab : ‖powerPair (row a μ α) (row b μ β) N‖ = a*b^(N-1)*‖L‖ := by
    rw [powerPair_normal_form a b μ α β N hN hβ]
    simp [L,abs_of_nonneg ha.le,abs_of_nonneg hb.le]
  have hba : ‖powerPair (row b μ β) (row a μ α) N‖ = b*a^(N-1)*‖L‖ := by
    rw [powerPair_normal_form b a μ β α N hN hα,hconj]
    simp [abs_of_nonneg ha.le,abs_of_nonneg hb.le]
  rw [haa,hbb,hab,hba]
  refine ⟨mul_pos (pow_pos ha _) hS,mul_pos (mul_pos ha (pow_pos hb _)) hL,
    mul_pos (pow_pos hb _) hS,?_⟩
  have hsquare : ‖L‖^2 < S^2 := by nlinarith
  have hpos : 0<a^N*b^N := mul_pos (pow_pos ha _) (pow_pos hb _)
  have hmul := mul_lt_mul_of_pos_left hsquare hpos
  have hap : a^(N-1)*a=a^N := pow_sub_one_mul (ne_of_gt hN) a
  have hbp : b^(N-1)*b=b^N := pow_sub_one_mul (ne_of_gt hN) b
  calc
    a*b^(N-1)*‖L‖*(b*a^(N-1)*‖L‖) =
        (a^(N-1)*a)*(b^(N-1)*b)*‖L‖^2 := by ring
    _ = (a^N*b^N)*‖L‖^2 := by rw [hap,hbp]
    _ < (a^N*b^N)*S^2 := hmul
    _ = a^N*S*(b^N*S) := by ring

/-- A bounded literal two-power matrix obstruction for normalized pure rows.
The hypotheses name actual magnitudes and phases; neither a matrix obstruction
nor a complexity conclusion is assumed. -/
theorem bounded_strict_minor {I : Type} [Fintype I] [DecidableEq I]
    (a b : ℝ) (ha : 0<a) (hb : 0<b) (block : D → I)
    (μ : I → ℝ) (hμ : ∀ i, 0<μ i) (hinj : Function.Injective μ)
    (α β : D → ℂ) (K : ℕ) (hK : 0<K)
    (hα : ∀ z, α z^K=1) (hβ : ∀ z, β z^K=1)
    (hd : ∃ i j, α i * star (β i) ≠ α j * star (β j))
    (hblock : ∃ i, (∑ z ∈ Finset.univ.filter (fun z => block z=i),
      α z * star (β z)) ≠ 0) :
    ∃ t : ℕ, 0<t ∧ t ≤ Fintype.card I ∧
      0 < ‖powerPair (row a (μ ∘ block) α) (row a (μ ∘ block) α) (t*K)‖ ∧
      0 < ‖powerPair (row a (μ ∘ block) α) (row b (μ ∘ block) β) (t*K)‖ ∧
      0 < ‖powerPair (row b (μ ∘ block) β) (row b (μ ∘ block) β) (t*K)‖ ∧
      ‖powerPair (row a (μ ∘ block) α) (row b (μ ∘ block) β) (t*K)‖ *
        ‖powerPair (row b (μ ∘ block) β) (row a (μ ∘ block) α) (t*K)‖ <
      ‖powerPair (row a (μ ∘ block) α) (row a (μ ∘ block) α) (t*K)‖ *
        ‖powerPair (row b (μ ∘ block) β) (row b (μ ∘ block) β) (t*K)‖ := by
  have hinj' : Function.Injective (fun i => μ i^K) := by
    intro i j he
    exact hinj ((pow_left_inj₀ (hμ i).le (hμ j).le (ne_of_gt hK)).mp he)
  have hnorm (z : D) : ‖α z * star (β z)‖=1 := by
    simp [Complex.norm_eq_one_of_pow_eq_one (hα z) (ne_of_gt hK),
      Complex.norm_eq_one_of_pow_eq_one (hβ z) (ne_of_gt hK)]
  obtain ⟨t,ht,htb,hL,hlt⟩ := PhaseObstruction.bounded_phase_obstruction block
    (fun i => μ i^K) (fun i => pow_pos (hμ i) _) hinj'
    (fun z => α z * star (β z)) hnorm hd hblock
  refine ⟨t,ht,htb,?_⟩
  apply strict_minor_of_phase_sum a b ha hb (μ ∘ block) α β (t*K) (Nat.mul_pos ht hK)
  · intro z
    rw [Nat.mul_comm t K,pow_mul,hα,one_pow]
  · intro z
    rw [Nat.mul_comm t K,pow_mul,hβ,one_pow]
  · simpa only [Function.comp_apply,Complex.ofReal_pow,←pow_mul,Nat.mul_comm K t] using hL
  · simpa only [Function.comp_apply,Complex.ofReal_pow,←pow_mul,Nat.mul_comm K t] using hlt

end ComplexCSP.PhasePowerAlgebra
