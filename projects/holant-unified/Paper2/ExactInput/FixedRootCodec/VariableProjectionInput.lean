import Paper2.ExactInput.FixedRootCodec.VariableProjectionMachines
import Paper2.ExactInput.FixedRootCodec.InputHeight

/-! Input-byte bounds and root coverage for the coefficient vectors returned
by the actual projection programs.
-/
namespace Paper2.ExactInput.FixedRootCodec.VariableProjection
open Computability Paper2.Algebraic Polynomial

theorem vector_polynomial_degree (d : ℕ) (v : Fin (d + 1) → ℚ) :
    (VariablePolynomial.polynomial v).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  have hn : ¬k < d + 1 := by omega
  simp [VariablePolynomial.coefficient_eq, hn]

theorem vector_polynomial_height {n : ℕ} (v : Fin n → ℚ) (j : ℕ) :
    rationalBitHeight ((VariablePolynomial.polynomial v).coeff j) ≤
      ((vectorEncoding n).encode v).length + 1 := by
  rw [VariablePolynomial.coefficient_eq]
  split_ifs with h
  · exact coordinate_height_input v ⟨j, h⟩
  · change 1 ≤ ((vectorEncoding n).encode v).length + 1
    omega

theorem projection_vectors_ne_zero (d : ℕ) (v : Fin (d + 1) → ℚ) :
    VariablePolynomial.polynomial (realPolynomialCoefficients d v) ≠ 0 ∧
      VariablePolynomial.polynomial (imaginaryPolynomialCoefficients d v) ≠ 0 := by
  rw [realPolynomialCoefficients_polynomial, imaginaryPolynomialCoefficients_polynomial]
  exact projection_polynomials_ne_zero _ _

theorem projection_vectors_degree (d : ℕ) (v : Fin (d + 1) → ℚ) :
    (VariablePolynomial.polynomial (realPolynomialCoefficients d v)).natDegree =
        (d + 1) * (d + 1) ∧
      (VariablePolynomial.polynomial (imaginaryPolynomialCoefficients d v)).natDegree =
        2 * ((d + 1) * (d + 1)) := by
  rw [realPolynomialCoefficients_polynomial, imaginaryPolynomialCoefficients_polynomial]
  exact projection_polynomials_degree _ _

theorem projection_vectors_cover (d : ℕ) (v : Fin (d + 1) → ℚ)
    (hp : VariablePolynomial.polynomial v ≠ 0) {z : ℂ}
    (hz : Polynomial.aeval z (VariablePolynomial.polynomial v) = 0) :
    Polynomial.aeval (z.re : ℂ)
        (VariablePolynomial.polynomial (realPolynomialCoefficients d v)) = 0 ∧
      Polynomial.aeval (z.im : ℂ)
        (VariablePolynomial.polynomial (imaginaryPolynomialCoefficients d v)) = 0 := by
  rw [realPolynomialCoefficients_polynomial, imaginaryPolynomialCoefficients_polynomial]
  exact projection_polynomials_cover _ _ hp (vector_polynomial_degree d v) hz

theorem real_eval_of_complex_aeval (p : ℚ[X]) (x : ℝ)
    (h : Polynomial.aeval (x : ℂ) p = 0) :
    (p.map (algebraMap ℚ ℝ)).eval x = 0 := by
  have hr : Polynomial.aeval x p = 0 := by
    apply Complex.ofReal_injective
    exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℝ ℂ) x p).symm.trans h
  simpa only [Polynomial.eval_map, ← Polynomial.aeval_def] using hr

/-- Coverage in the real evaluation form used by the Sturm root counter. -/
theorem projection_vectors_real_cover (d : ℕ) (v : Fin (d + 1) → ℚ)
    (hp : VariablePolynomial.polynomial v ≠ 0) {z : ℂ}
    (hz : Polynomial.aeval z (VariablePolynomial.polynomial v) = 0) :
    ((VariablePolynomial.polynomial (realPolynomialCoefficients d v)).map
        (algebraMap ℚ ℝ)).eval z.re = 0 ∧
      ((VariablePolynomial.polynomial (imaginaryPolynomialCoefficients d v)).map
        (algebraMap ℚ ℝ)).eval z.im = 0 := by
  obtain ⟨hr, hi⟩ := projection_vectors_cover d v hp hz
  exact ⟨real_eval_of_complex_aeval _ _ hr, real_eval_of_complex_aeval _ _ hi⟩

/-- Precision is selected from the encoded coefficient vector itself. -/
theorem projection_vectors_input_height (d : ℕ) :
    ∃ C : ℕ, ∀ v : Fin (d + 1) → ℚ,
      (∀ j, rationalBitHeight
        ((VariablePolynomial.polynomial (realPolynomialCoefficients d v)).coeff j) ≤
          C * (((vectorEncoding (d + 1)).encode v).length + 2)) ∧
      (∀ j, rationalBitHeight
        ((VariablePolynomial.polynomial (imaginaryPolynomialCoefficients d v)).coeff j) ≤
          C * (((vectorEncoding (d + 1)).encode v).length + 2)) := by
  obtain ⟨C, hC⟩ := projection_polynomials_height d
  refine ⟨C, fun v => ?_⟩
  have hh := hC (((vectorEncoding (d + 1)).encode v).length + 1)
    (VariablePolynomial.polynomial v) (vector_polynomial_height v)
  rw [realPolynomialCoefficients_polynomial, imaginaryPolynomialCoefficients_polynomial]
  simpa only [Nat.add_assoc] using hh

end Paper2.ExactInput.FixedRootCodec.VariableProjection
