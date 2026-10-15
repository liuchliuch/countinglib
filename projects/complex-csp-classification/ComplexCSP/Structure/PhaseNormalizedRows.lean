import ComplexCSP.Structure.PhasePowerAlgebra
import ComplexCSP.Structure.BlockOrthogonality

/-! # From literal non-BO normalized rows to the bounded two-power obstruction -/
noncomputable section
namespace ComplexCSP.PhaseNormalizedRows
open scoped BigOperators
open PhasePowerAlgebra BlockOrthogonality RowTypes
variable {D : Type} [Fintype D]

omit [Fintype D] in
theorem proportional_of_constant_relative (b : ℝ) (hb : 0<b) (μ : D → ℝ)
    (α β : D → ℂ) (hα : ∀ z, ‖α z‖=1) (hβ : ∀ z, ‖β z‖=1)
    (z₀ : D) (hconst : ∀ z, α z*star (β z)=α z₀*star (β z₀)) :
    Proportional (row 1 μ α) (row b μ β) := by
  let δ := α z₀*star (β z₀)
  have hδ : δ ≠ 0 := by
    have hn : ‖δ‖=1 := by simp [δ,hα,hβ]
    intro hz
    simp [hz] at hn
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  refine ⟨δ/(b : ℂ),div_ne_zero hδ hb0,?_⟩
  intro z
  have hunit : star (β z)*β z=1 := by
    rw [mul_comm]
    change β z*(starRingEnd ℂ) (β z)=1
    rw [Complex.mul_conj',hβ]
    norm_num
  have he : α z=δ*β z := by
    dsimp only [δ]
    rw [←hconst z,mul_assoc,hunit,mul_one]
  simp only [row,Complex.ofReal_one,one_mul,he]
  field_simp

/-- Actual failed block orthogonality of normalized pure rows produces a
strict principal magnitude minor, with t bounded by the column count. -/
theorem bounded_obstruction [Nonempty D] (b : ℝ) (hb : 0<b)
    (μ : D → ℝ) (hμ : ∀ z, 0<μ z) (α β : D → ℂ)
    (K : ℕ) (hK : 0<K) (hα : ∀ z, α z^K=1) (hβ : ∀ z, β z^K=1)
    (hind : ¬Proportional (row 1 μ α) (row b μ β))
    (horth : ¬VectorBlockOrthogonal (row 1 μ α) (row b μ β)) :
    ∃ t : ℕ, 0<t ∧ t ≤ Fintype.card D ∧
      0 < ‖powerPair (row 1 μ α) (row 1 μ α) (t*K)‖ ∧
      0 < ‖powerPair (row 1 μ α) (row b μ β) (t*K)‖ ∧
      0 < ‖powerPair (row b μ β) (row b μ β) (t*K)‖ ∧
      ‖powerPair (row 1 μ α) (row b μ β) (t*K)‖ *
        ‖powerPair (row b μ β) (row 1 μ α) (t*K)‖ <
      ‖powerPair (row 1 μ α) (row 1 μ α) (t*K)‖ *
        ‖powerPair (row b μ β) (row b μ β) (t*K)‖ := by
  classical
  have hαnorm (z : D) : ‖α z‖=1 := Complex.norm_eq_one_of_pow_eq_one (hα z) (ne_of_gt hK)
  have hβnorm (z : D) : ‖β z‖=1 := Complex.norm_eq_one_of_pow_eq_one (hβ z) (ne_of_gt hK)
  have hd : ∃ i j, α i*star (β i) ≠ α j*star (β j) := by
    by_contra h
    push_neg at h
    exact hind (proportional_of_constant_relative b hb μ α β hαnorm hβnorm
      (Classical.arbitrary D) (fun z => h z _))
  let I := Set.range μ
  letI : Fintype I := (Set.finite_range μ).fintype
  let block : D → I := fun z => ⟨μ z,⟨z,rfl⟩⟩
  let mag : I → ℝ := Subtype.val
  have hmag : ∀ i, 0 < mag i := by
    rintro ⟨v,z,rfl⟩
    exact hμ z
  have hinj : Function.Injective mag := Subtype.val_injective
  have hnorm (z : D) : ‖row 1 μ α z‖=μ z := by
    simp [row,hαnorm,abs_of_nonneg (hμ z).le]
  have hblock : ∃ i : I,
      (∑ z ∈ Finset.univ.filter (fun z => block z=i),α z*star (β z)) ≠ 0 := by
    unfold VectorBlockOrthogonal at horth
    push_neg at horth
    obtain ⟨z,hz,hs⟩ := horth
    refine ⟨block z,?_⟩
    intro he
    apply hs
    have hB : magnitudeBlock (row 1 μ α) z =
        Finset.univ.filter (fun w => block w=block z) := by
      ext w
      simp [magnitudeBlock,hnorm,block]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [hermitianSum,hB]
    calc
      _ = ((b : ℂ)*(μ z : ℂ)^2) *
          ∑ w ∈ Finset.univ.filter (fun w => block w=block z),α w*star (β w) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w hw
        have hm : μ w=μ z := congrArg Subtype.val (Finset.mem_filter.mp hw).2
        simp only [row,Complex.ofReal_one,one_mul,star_mul,Complex.star_def,
          Complex.conj_ofReal,hm]
        ring
      _ = 0 := by rw [he,mul_zero]
  obtain ⟨t,ht,htb,hminor⟩ := PhasePowerAlgebra.bounded_strict_minor
    1 b (by norm_num) hb block mag hmag hinj α β K hK hα hβ hd hblock
  have hcard : Fintype.card I ≤ Fintype.card D := Fintype.card_range_le μ
  exact ⟨t,ht,htb.trans hcard,hminor⟩

end ComplexCSP.PhaseNormalizedRows
