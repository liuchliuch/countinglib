import Paper2.ExactInput.MvPolynomialHeight
import Paper2.ExactInput.CoordinateOutputBound
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-! A genuine fixed-degree monic annihilator of the original Holant output has
polynomial-size rational coefficients. It is the characteristic polynomial of
multiplication in the one field derived from the literal original language.
This file does not equate that polynomial with the minimal polynomial. -/
namespace Paper2.ExactInput
open Paper2.Algebraic Paper2.Tractable Paper2.Problem
open scoped BigOperators

noncomputable def leftMulPolynomial {K : Type*} [Field K] [Algebra ℚ K]
    {n : ℕ} (F : FixedField K n) (i j : Fin n) : MvPolynomial (Fin n) ℚ :=
  ∑ k, MvPolynomial.C (Algebra.leftMulMatrix F.basis (F.basis k) i j) * MvPolynomial.X k

theorem eval_leftMulPolynomial {K : Type*} [Field K] [Algebra ℚ K]
    {n : ℕ} (F : FixedField K n) (v : Fin n → ℚ) (i j : Fin n) :
    MvPolynomial.eval v (leftMulPolynomial F i j) =
      Algebra.leftMulMatrix F.basis (F.decode v) i j := by
  rw [show F.decode v = ∑ k, v k • F.basis k from F.basis.equivFun_symm_apply v]
  simp [leftMulPolynomial, map_smul, mul_comm, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

noncomputable def fixedAnnihilator {K : Type*} [Field K] [Algebra ℚ K]
    {n : ℕ} (F : FixedField K n) (v : Fin n → ℚ) : Polynomial ℚ :=
  (Algebra.leftMulMatrix F.basis (F.decode v)).charpoly

theorem fixedAnnihilator_monic {K : Type*} [Field K] [Algebra ℚ K]
    {n : ℕ} (F : FixedField K n) (v : Fin n → ℚ) : (fixedAnnihilator F v).Monic :=
  Matrix.charpoly_monic _

theorem fixedAnnihilator_natDegree {K : Type*} [Field K] [Algebra ℚ K]
    {n : ℕ} (F : FixedField K n) (v : Fin n → ℚ) : (fixedAnnihilator F v).natDegree = n := by
  simp [fixedAnnihilator, Matrix.charpoly_natDegree_eq_dim]

theorem fixedAnnihilator_aeval {K : Type*} [Field K] [Algebra ℚ K]
    {n : ℕ} (F : FixedField K n) (v : Fin n → ℚ) :
    Polynomial.aeval (F.decode v) (fixedAnnihilator F v) = 0 := by
  apply (injective_iff_map_eq_zero (G := K) (Algebra.leftMulMatrix F.basis)).mp
    (Algebra.leftMulMatrix_injective F.basis)
  rw [← Polynomial.aeval_algHom_apply]
  exact Matrix.aeval_self_charpoly _

/-- All coefficients, including those beyond the degree, obey a fixed affine
bit-height bound in the original coordinate bit heights. -/
theorem fixedAnnihilator_height_bound {K : Type*} [Field K] [Algebra ℚ K]
    {n : ℕ} (F : FixedField K n) :
    ∃ C : ℕ, ∀ (B : ℕ) (v : Fin n → ℚ), (∀ i, rationalBitHeight (v i) ≤ B) →
      ∀ j, rationalBitHeight ((fixedAnnihilator F v).coeff j) ≤ C * (B + 1) := by
  obtain ⟨A, hA⟩ := mvPolynomial_family_height_bound
    (fun ij : Fin n × Fin n => leftMulPolynomial F ij.1 ij.2)
  obtain ⟨D, hD⟩ := mvPolynomial_family_height_bound
    (fun j : Fin (n + 1) => (Matrix.charpoly.univ ℚ (Fin n)).coeff j.val)
  refine ⟨D * (A + 1) + 1, fun B v hv j => ?_⟩
  by_cases hj : j < n + 1
  · have he : ∀ ij : Fin n × Fin n,
        rationalBitHeight (Algebra.leftMulMatrix F.basis (F.decode v) ij.1 ij.2) ≤
          A * (B + 1) := by
      intro ij
      simpa only [eval_leftMulPolynomial] using hA B v hv ij
    have hd := hD (A * (B + 1))
      (fun ij : Fin n × Fin n => Algebra.leftMulMatrix F.basis (F.decode v) ij.1 ij.2)
      he ⟨j, hj⟩
    have heval := Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id ℚ)
      (fun ij : Fin n × Fin n => Algebra.leftMulMatrix F.basis (F.decode v) ij.1 ij.2) j
    change MvPolynomial.eval _ _ = (fixedAnnihilator F v).coeff j at heval
    rw [heval] at hd
    nlinarith
  · have hd : (fixedAnnihilator F v).natDegree < j := by
      rw [fixedAnnihilator_natDegree]
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd]
    change 1 ≤ (D * (A + 1) + 1) * (B + 1)
    have hpos : 0 < (D * (A + 1) + 1) * (B + 1) := Nat.mul_pos (by omega) (by omega)
    omega

/-- The same genuine annihilator has coefficients with at most polynomially many
bits in the encoded original graph size. The polynomial depends only on L and w. -/
theorem output_annihilator_polynomial_bound (w : Wiring) (L : Language) :
    ∃ P : Polynomial ℕ, ∀ G : Instance L, ∀ j,
      rationalBitHeight ((fixedAnnihilator L.fieldPresentation (outputCoordinates w L G)).coeff j) ≤
        P.eval ((inputEncoding L).encode G).length := by
  obtain ⟨C, hC⟩ := fixedAnnihilator_height_bound L.fieldPresentation
  refine ⟨Polynomial.C C * (coordinateOutputPolynomial w L + 1), fun G j => ?_⟩
  have h := hC ((coordinateOutputPolynomial w L).eval ((inputEncoding L).encode G).length)
    (outputCoordinates w L G) (fun i => ?_) j
  · simpa using h
  · unfold rationalBitHeight rationalHeight
    apply Nat.size_le.mpr
    exact max_lt (Nat.size_le.mp (output_coordinate_num_den_bits w L G i).1)
      (Nat.size_le.mp (output_coordinate_num_den_bits w L G i).2)

end Paper2.ExactInput
