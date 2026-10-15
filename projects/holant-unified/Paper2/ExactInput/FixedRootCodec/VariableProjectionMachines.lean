import Paper2.ExactInput.FixedRootCodec.VariableProjectionHeight
import Paper2.ExactInput.FixedRootCodec.VariablePolynomial

/-! Actual finite rational programs for the projection coefficients. Symbolic
characteristic polynomials are fixed program descriptions. A descending scan
of the fixed coefficient vector selects its literal leading coefficient;
normalization uses the proved total rational reciprocal program.
-/
namespace Paper2.ExactInput.FixedRootCodec.VariableProjection
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines Polynomial
noncomputable section

/-- Fixed multivariate rational polynomial circuits are compiled from genuine
scalar programs. Only the variable coefficient vector remains runtime input. -/
def symbolicComputes {n : ℕ} (p : MvPolynomial (Fin n) ℚ) :
    Computes (vectorEncoding n) rationalEncoding (fun v => MvPolynomial.eval v p) :=
  Classical.choice (by
    induction p using MvPolynomial.induction_on with
    | C a =>
        exact ⟨congrComputes (constantComputes (vectorEncoding n) rationalEncoding a)
          (fun v => by simp)⟩
    | add p q hp hq =>
        obtain ⟨u⟩ := hp
        obtain ⟨w⟩ := hq
        exact ⟨congrComputes (rationalProvider.addComputes u w)
          (fun v => by simp)⟩
    | mul_X p i hp =>
        obtain ⟨u⟩ := hp
        exact ⟨congrComputes (rationalProvider.mulComputes u (coordinateComputes n i))
          (fun v => by simp)⟩)

def realCoefficients {n : ℕ} (v : Fin n → ℚ) : Fin (n * n + 1) → ℚ :=
  fun j => (realProjection v).coeff j.val

def imaginaryCoefficients {n : ℕ} (v : Fin n → ℚ) : Fin (2 * (n * n) + 1) → ℚ :=
  fun j => (imaginaryProjection v).coeff j.val

def realCoefficientsComputes (n : ℕ) :
    Computes (vectorEncoding n) (vectorEncoding (n * n + 1)) (realCoefficients (n := n)) :=
  assembleComputes (vectorEncoding n) (n * n + 1) _ (fun j =>
    congrComputes (symbolicComputes ((realSymbolic n).coeff j.val))
      (fun v => by rw [realCoefficients, realProjection, Polynomial.coeff_map]))

def imaginaryCoefficientsComputes (n : ℕ) :
    Computes (vectorEncoding n) (vectorEncoding (2 * (n * n) + 1))
      (imaginaryCoefficients (n := n)) :=
  assembleComputes (vectorEncoding n) (2 * (n * n) + 1) _ (fun j =>
    congrComputes (symbolicComputes ((imaginarySymbolic n).coeff j.val))
      (fun v => by rw [imaginaryCoefficients, imaginaryProjection, Polynomial.coeff_map]))

theorem realCoefficients_polynomial {n : ℕ} (v : Fin n → ℚ) :
    VariablePolynomial.polynomial (realCoefficients v) = realProjection v := by
  unfold VariablePolynomial.polynomial realCoefficients
  rw [Fin.sum_univ_eq_sum_range
    (fun i => Polynomial.monomial i ((realProjection v).coeff i))]
  exact (Polynomial.as_sum_range' _ _ (by rw [realProjection_degree]; omega)).symm

theorem imaginaryCoefficients_polynomial {n : ℕ} (v : Fin n → ℚ) :
    VariablePolynomial.polynomial (imaginaryCoefficients v) = imaginaryProjection v := by
  unfold VariablePolynomial.polynomial imaginaryCoefficients
  rw [Fin.sum_univ_eq_sum_range
    (fun i => Polynomial.monomial i ((imaginaryProjection v).coeff i))]
  exact (Polynomial.as_sum_range' _ _ (by rw [imaginaryProjection_degree]; omega)).symm

def normalizeAt (d : ℕ) (j : Fin (d + 1)) (v : Fin (d + 1) → ℚ)
    (i : Fin (d + 1)) : ℚ :=
  if h : d + 1 - j.val ≤ i.val then v ⟨i.val - (d + 1 - j.val), by omega⟩ / v j else 0

def normalizeAtComputes (d : ℕ) (j : Fin (d + 1)) :
    Computes (vectorEncoding (d + 1)) (vectorEncoding (d + 1)) (normalizeAt d j) := by
  apply assembleComputes
  intro i
  by_cases h : d + 1 - j.val ≤ i.val
  · exact congrComputes
      ((pairComputes (coordinateComputes (d + 1) ⟨i.val - (d + 1 - j.val), by omega⟩)
        (coordinateComputes (d + 1) j)).andThen VariablePolynomial.divisionComputes)
      (fun v => by simp [normalizeAt, h])
  · exact congrComputes (constantComputes _ rationalEncoding 0)
      (fun v => by simp [normalizeAt, h])

theorem normalizeAt_correct (d : ℕ) (j : Fin (d + 1)) (v : Fin (d + 1) → ℚ)
    (hd : (VariablePolynomial.polynomial v).natDegree = j.val) :
    normalizeAt d j v = paddedCoefficients d (VariablePolynomial.polynomial v) := by
  funext i
  unfold paddedCoefficients VariableSeparation.paddedPolynomial
  rw [coeff_mul_X_pow']
  simp only [hd]
  by_cases h : d + 1 - j.val ≤ i.val
  · have hi : i.val - (d + 1 - j.val) < d + 1 := by omega
    simp only [h, ite_true, coeff_mul_C, Polynomial.leadingCoeff, hd,
      VariablePolynomial.coefficient_eq, hi, j.isLt, dite_true]
    simp [normalizeAt, h, div_eq_mul_inv]
  · simp [normalizeAt, h]

def normalizeDown (d : ℕ) : ℕ → (Fin (d + 1) → ℚ) → Fin (d + 1) → ℚ
  | 0, _ => fun _ => 0
  | r + 1, v => if h : r < d + 1 then
      if v ⟨r, h⟩ = 0 then normalizeDown d r v else normalizeAt d ⟨r, h⟩ v
    else normalizeDown d r v

def normalizeDownComputes (d : ℕ) : (r : ℕ) →
    Computes (vectorEncoding (d + 1)) (vectorEncoding (d + 1)) (normalizeDown d r)
  | 0 => constantComputes _ _ (fun _ => 0)
  | r + 1 => by
    by_cases h : r < d + 1
    · exact congrComputes (ifComputes
        ((coordinateComputes (d + 1) ⟨r, h⟩).andThen
          (FixedRootCodec.zeroComputes rationalEncoding))
        (normalizeDownComputes d r) (normalizeAtComputes d ⟨r, h⟩))
        (fun v => by simp only [normalizeDown, h, dite_true, Function.comp_apply,
          decide_eq_true_eq])
    · exact congrComputes (normalizeDownComputes d r)
        (fun v => by simp [normalizeDown, h])

private theorem normalizeDown_correct (d r : ℕ) (hr : r ≤ d + 1)
    (v : Fin (d + 1) → ℚ) (hv : ∀ i, r ≤ i.val → v i = 0) :
    normalizeDown d r v = paddedCoefficients d (VariablePolynomial.polynomial v) := by
  induction r with
  | zero =>
      have hp : VariablePolynomial.polynomial v = 0 := by
        ext k
        rw [VariablePolynomial.coefficient_eq]
        split_ifs
        · exact hv _ (Nat.zero_le _)
        · rfl
      funext i
      simp [normalizeDown, paddedCoefficients, VariableSeparation.paddedPolynomial, hp]
  | succ r ih =>
      have h : r < d + 1 := by omega
      simp only [normalizeDown, h, dite_true]
      by_cases hz : v ⟨r, h⟩ = 0
      · rw [ite_eq_left hz]
        apply ih (by omega)
        intro i hi
        by_cases he : i.val = r
        · have hfin : i = (⟨r, h⟩ : Fin (d + 1)) := Fin.ext he
          simpa only [hfin] using hz
        · exact hv i (by omega)
      · rw [ite_eq_right hz]
        apply normalizeAt_correct
        change (VariablePolynomial.polynomial v).natDegree = r
        apply natDegree_eq_of_le_of_coeff_ne_zero
        · apply natDegree_le_iff_coeff_eq_zero.mpr
          intro k hk
          rw [VariablePolynomial.coefficient_eq]
          split_ifs
          · exact hv _ (by change r + 1 ≤ k; omega)
          · rfl
        · simpa only [VariablePolynomial.coefficient_eq, h, dite_true] using hz

def normalizedCoefficients (d : ℕ) (v : Fin (d + 1) → ℚ) : Fin (d + 1) → ℚ :=
  normalizeDown d (d + 1) v

def normalizedCoefficientsComputes (d : ℕ) :
    Computes (vectorEncoding (d + 1)) (vectorEncoding (d + 1)) (normalizedCoefficients d) :=
  normalizeDownComputes d (d + 1)

theorem normalizedCoefficients_correct (d : ℕ) (v : Fin (d + 1) → ℚ) :
    normalizedCoefficients d v = paddedCoefficients d (VariablePolynomial.polynomial v) :=
  normalizeDown_correct d (d + 1) le_rfl v (fun i hi => by omega)

def realPolynomialCoefficients (d : ℕ) (v : Fin (d + 1) → ℚ) :
    Fin ((d + 1) * (d + 1) + 1) → ℚ := realCoefficients (normalizedCoefficients d v)

def imaginaryPolynomialCoefficients (d : ℕ) (v : Fin (d + 1) → ℚ) :
    Fin (2 * ((d + 1) * (d + 1)) + 1) → ℚ := imaginaryCoefficients (normalizedCoefficients d v)

def realPolynomialCoefficientsComputes (d : ℕ) :
    Computes (vectorEncoding (d + 1)) (vectorEncoding ((d + 1) * (d + 1) + 1))
      (realPolynomialCoefficients d) :=
  (normalizedCoefficientsComputes d).andThen (realCoefficientsComputes (d + 1))

def imaginaryPolynomialCoefficientsComputes (d : ℕ) :
    Computes (vectorEncoding (d + 1)) (vectorEncoding (2 * ((d + 1) * (d + 1)) + 1))
      (imaginaryPolynomialCoefficients d) :=
  (normalizedCoefficientsComputes d).andThen (imaginaryCoefficientsComputes (d + 1))

theorem realPolynomialCoefficients_polynomial (d : ℕ) (v : Fin (d + 1) → ℚ) :
    VariablePolynomial.polynomial (realPolynomialCoefficients d v) =
      realPolynomial d (VariablePolynomial.polynomial v) := by
  rw [realPolynomialCoefficients, realCoefficients_polynomial, normalizedCoefficients_correct]
  rfl

theorem imaginaryPolynomialCoefficients_polynomial (d : ℕ) (v : Fin (d + 1) → ℚ) :
    VariablePolynomial.polynomial (imaginaryPolynomialCoefficients d v) =
      imaginaryPolynomial d (VariablePolynomial.polynomial v) := by
  rw [imaginaryPolynomialCoefficients, imaginaryCoefficients_polynomial,
    normalizedCoefficients_correct]
  rfl

end
end Paper2.ExactInput.FixedRootCodec.VariableProjection
