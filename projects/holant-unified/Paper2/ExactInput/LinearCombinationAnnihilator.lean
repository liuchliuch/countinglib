import Paper2.ExactInput.AnnihilatorHeight

/-! Fixed linear combinations in a finite rational algebra have genuine monic
annihilators of bounded coefficient bit height. This also applies to K tensor K,
which is not required to be a field. -/
namespace Paper2.ExactInput
open Paper2.Algebraic
open scoped BigOperators

section
variable {A ι τ : Type*} [Ring A] [Algebra ℚ A]
  [Fintype ι] [DecidableEq ι] [Fintype τ]

noncomputable def combinationAnnihilator (b : Module.Basis ι ℚ A) (e : τ → A)
    (v : τ → ℚ) : Polynomial ℚ :=
  (Algebra.leftMulMatrix b (∑ t, v t • e t)).charpoly

theorem combinationAnnihilator_monic (b : Module.Basis ι ℚ A) (e : τ → A)
    (v : τ → ℚ) : (combinationAnnihilator b e v).Monic := Matrix.charpoly_monic _

theorem combinationAnnihilator_aeval (b : Module.Basis ι ℚ A) (e : τ → A)
    (v : τ → ℚ) : Polynomial.aeval (∑ t, v t • e t) (combinationAnnihilator b e v) = 0 := by
  apply (injective_iff_map_eq_zero (G := A) (Algebra.leftMulMatrix b)).mp
    (Algebra.leftMulMatrix_injective b)
  rw [← Polynomial.aeval_algHom_apply]
  exact Matrix.aeval_self_charpoly _

/-- The constant is determined before the input coordinate vector is read. -/
theorem combinationAnnihilator_height_bound (b : Module.Basis ι ℚ A) (e : τ → A) :
    ∃ C : ℕ, ∀ (B : ℕ) (v : τ → ℚ), (∀ i, rationalBitHeight (v i) ≤ B) →
      ∀ j, rationalBitHeight ((combinationAnnihilator b e v).coeff j) ≤ C * (B + 1) := by
  let P : ι × ι → MvPolynomial τ ℚ := fun ij =>
    ∑ t, MvPolynomial.C (Algebra.leftMulMatrix b (e t) ij.1 ij.2) * MvPolynomial.X t
  have hP : ∀ v : τ → ℚ, ∀ ij : ι × ι,
      MvPolynomial.eval v (P ij) = Algebra.leftMulMatrix b (∑ t, v t • e t) ij.1 ij.2 := by
    intro v ij
    simp [P, map_smul, mul_comm, Matrix.sum_apply, Matrix.smul_apply]
  obtain ⟨C, hC⟩ := mvPolynomial_family_height_bound P
  obtain ⟨D, hD⟩ := mvPolynomial_family_height_bound
    (fun j : Fin (Fintype.card ι + 1) => (Matrix.charpoly.univ ℚ ι).coeff j.val)
  refine ⟨D * (C + 1) + 1, fun B v hv j => ?_⟩
  by_cases hj : j < Fintype.card ι + 1
  · have he : ∀ ij : ι × ι,
        rationalBitHeight (Algebra.leftMulMatrix b (∑ t, v t • e t) ij.1 ij.2) ≤ C * (B + 1) := by
      intro ij
      simpa only [hP] using hC B v hv ij
    have hd := hD (C * (B + 1))
      (fun ij : ι × ι => Algebra.leftMulMatrix b (∑ t, v t • e t) ij.1 ij.2) he ⟨j, hj⟩
    have heval := Matrix.charpoly.univ_coeff_eval₂Hom ι (RingHom.id ℚ)
      (fun ij : ι × ι => Algebra.leftMulMatrix b (∑ t, v t • e t) ij.1 ij.2) j
    change MvPolynomial.eval _ _ = (combinationAnnihilator b e v).coeff j at heval
    rw [heval] at hd
    nlinarith
  · have hdeg : (combinationAnnihilator b e v).natDegree < j := by
      simpa [combinationAnnihilator, Matrix.charpoly_natDegree_eq_dim] using
        (show Fintype.card ι < j by omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg]
    change 1 ≤ (D * (C + 1) + 1) * (B + 1)
    have hpos : 0 < (D * (C + 1) + 1) * (B + 1) := Nat.mul_pos (by omega) (by omega)
    omega

end
end Paper2.ExactInput
