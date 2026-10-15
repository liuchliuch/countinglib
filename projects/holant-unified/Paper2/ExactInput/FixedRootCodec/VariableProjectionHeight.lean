import Paper2.ExactInput.FixedRootCodec.VariableProjection

/-! The actual symbolic projection coefficients have affine rational bit-height
bounds. The constants depend on the fixed maximum degree only.
-/
namespace Paper2.ExactInput.FixedRootCodec.VariableProjection
open Paper2.Algebraic Polynomial
noncomputable section

private theorem symbolic_height (n m : ℕ) (P : Polynomial (MvPolynomial (Fin n) ℚ))
    (hd : ∀ v : Fin n → ℚ, (P.map (MvPolynomial.eval v)).natDegree ≤ m) :
    ∃ C : ℕ, ∀ B (v : Fin n → ℚ), (∀ i, rationalBitHeight (v i) ≤ B) →
      ∀ j, rationalBitHeight ((P.map (MvPolynomial.eval v)).coeff j) ≤ C * (B + 1) := by
  obtain ⟨C, hC⟩ := mvPolynomial_family_height_bound
    (fun j : Fin (m + 1) => P.coeff j.val)
  refine ⟨C + 1, fun B v hv j => ?_⟩
  by_cases hj : j < m + 1
  · rw [Polynomial.coeff_map]
    exact (hC B v hv ⟨j, hj⟩).trans (Nat.mul_le_mul_right _ (by omega))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hd v; omega)]
    change 1 ≤ (C + 1) * (B + 1)
    have := Nat.mul_pos (by omega : 0 < C + 1) (by omega : 0 < B + 1)
    omega

theorem realProjection_height (n : ℕ) :
    ∃ C : ℕ, ∀ B (v : Fin n → ℚ), (∀ i, rationalBitHeight (v i) ≤ B) →
      ∀ j, rationalBitHeight ((realProjection v).coeff j) ≤ C * (B + 1) :=
  symbolic_height n (n * n) (realSymbolic n)
    (fun v => (realProjection_degree v).le)

theorem imaginaryProjection_height (n : ℕ) :
    ∃ C : ℕ, ∀ B (v : Fin n → ℚ), (∀ i, rationalBitHeight (v i) ≤ B) →
      ∀ j, rationalBitHeight ((imaginaryProjection v).coeff j) ≤ C * (B + 1) :=
  symbolic_height n (2 * (n * n)) (imaginarySymbolic n)
    (fun v => (imaginaryProjection_degree v).le)

theorem projection_polynomials_height (d : ℕ) :
    ∃ C : ℕ, ∀ B (p : ℚ[X]), (∀ j, rationalBitHeight (p.coeff j) ≤ B) →
      (∀ j, rationalBitHeight ((realPolynomial d p).coeff j) ≤ C * (B + 1)) ∧
      (∀ j, rationalBitHeight ((imaginaryPolynomial d p).coeff j) ≤ C * (B + 1)) := by
  obtain ⟨C, hC⟩ := realProjection_height (d + 1)
  obtain ⟨D, hD⟩ := imaginaryProjection_height (d + 1)
  refine ⟨2 * (C + D), fun B p hp => ?_⟩
  have hv : ∀ i : Fin (d + 1), rationalBitHeight (paddedCoefficients d p i) ≤
      2 * B + 1 := fun i => VariableSeparation.paddedPolynomial_height d B p hp i.val
  constructor
  · intro j
    have hb := hC (2 * B + 1) (paddedCoefficients d p) hv j
    change rationalBitHeight ((realProjection (paddedCoefficients d p)).coeff j) ≤ _
    nlinarith
  · intro j
    have hb := hD (2 * B + 1) (paddedCoefficients d p) hv j
    change rationalBitHeight ((imaginaryProjection (paddedCoefficients d p)).coeff j) ≤ _
    nlinarith

end
end Paper2.ExactInput.FixedRootCodec.VariableProjection
