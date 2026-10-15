import Paper2.ExactInput.DyadicIsolation

/-! Public descriptor lengths from degree, coefficient height and grid precision.
All framing and all four strict rectangle endpoints are counted. -/
namespace Paper2.ExactInput
open Paper2.Algebraic Polynomial
open scoped BigOperators

theorem dense_polynomial_length_le (p : Polynomial ℚ) (D B : ℕ)
    (hD : p.natDegree ≤ D) (hB : ∀ j, rationalBitHeight (p.coeff j) ≤ B) :
    (polynomialEncoding.encode (densePolynomialCode p)).length ≤
      1 + (D + 1) * (4 * D.size + 4 * (B + 1) + 4) := by
  rw [polynomialEncoding_length]
  simp only [densePolynomialCode, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _i : Fin (p.natDegree + 1), (4 * D.size + 4 * (B + 1) + 4) := by
      apply Finset.sum_le_sum
      intro i _
      have hi : i.val.size ≤ D.size := Nat.size_le_size (by omega)
      have hc := (rationalEncoding_length_le_height (p.coeff i.val)).trans
        (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (hB i.val) 1))
      omega
    _ = (p.natDegree + 1) * (4 * D.size + 4 * (B + 1) + 4) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

theorem grid_height_magnitude_le (C S B : ℕ) :
    (6 * 2 ^ S) * (C * 2 ^ B + 1) + 3 ≤ 24 * (C + 1) * 2 ^ (S + B) := by
  have hpow : 1 ≤ 2 ^ B := Nat.one_le_pow _ _ (by omega)
  have hq : 0 < 6 * 2 ^ S := by positivity
  have hbase : 0 < (6 * 2 ^ S) * (C * 2 ^ B + 1) := Nat.mul_pos hq (by omega)
  calc
    _ ≤ 4 * ((6 * 2 ^ S) * (C * 2 ^ B + 1)) := by omega
    _ ≤ 4 * ((6 * 2 ^ S) * ((C + 1) * 2 ^ B)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      nlinarith
    _ = _ := by rw [pow_add]; ring

theorem grid_height_bits_le (C S B : ℕ) :
    ((6 * 2 ^ S) * (C * 2 ^ B + 1) + 3).size ≤
      (24 * (C + 1)).size + S + B + 1 := by
  have h := (Nat.size_le_size (grid_height_magnitude_le C S B)).trans
    (natSize_mul_le (24 * (C + 1)) (2 ^ (S + B)))
  rw [Nat.size_pow] at h
  omega

/-- All four endpoints have this bit bound, including the floor integers' signs. -/
theorem grid_endpoint_bits (a : ℝ) (C S B : ℕ) (ha : |a| ≤ C * (2 : ℝ) ^ B) :
    rationalBitHeight (gridLower a (6 * 2 ^ S)) ≤ (24 * (C + 1)).size + S + B + 1 ∧
    rationalBitHeight (gridUpper a (6 * 2 ^ S)) ≤ (24 * (C + 1)).size + S + B + 1 := by
  have ha' : |a| ≤ ((C * 2 ^ B : ℕ) : ℝ) := by exact_mod_cast ha
  have h := grid_endpoint_heights a (Q := 6 * 2 ^ S) (by positivity) ha'
  exact ⟨(Nat.size_le_size h.1).trans (grid_height_bits_le C S B),
    (Nat.size_le_size h.2).trans (grid_height_bits_le C S B)⟩

end Paper2.ExactInput
