import Paper2.ExactInput.MinimalPolynomialHeight
import Paper2.ExactInput.RootSeparation
import Paper2.ExactInput.DescriptorLength

/-! Polynomial-length strict public root answers for every finite original
language. This is an existence theorem, not a runtime assertion for converting
coordinates or deciding arbitrary raw descriptors. -/
namespace Paper2.ExactInput
open Paper2.Algebraic Paper2.Tractable Paper2.Complexity Paper2.Problem Polynomial

/-- The byte budget includes a dense minimal polynomial and all four signed
rational grid endpoints, with the exact framing used by `rootEncoding`. -/
theorem grid_descriptor_length_le (p : Polynomial ℚ) (z : ℂ) (D H C S B : ℕ)
    (hD : p.natDegree ≤ D) (hH : ∀ j, rationalBitHeight (p.coeff j) ≤ H)
    (hz : ‖z‖ ≤ C * (2 : ℝ) ^ B) :
    (rootEncoding.encode ⟨densePolynomialCode p, gridRectangle z (6 * 2 ^ S)⟩).length ≤
      2 * (1 + (D + 1) * (4 * D.size + 4 * (H + 1) + 4)) +
        14 * ((24 * (C + 1)).size + S + B + 2) + 4 := by
  have hp := dense_polynomial_length_le p D H hD hH
  have hre := grid_endpoint_bits z.re C S B ((Complex.abs_re_le_norm z).trans hz)
  have him := grid_endpoint_bits z.im C S B ((Complex.abs_im_le_norm z).trans hz)
  have hloR := (rationalEncoding_length_le_height (gridLower z.re (6 * 2 ^ S))).trans
    (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hre.1 1))
  have hhiR := (rationalEncoding_length_le_height (gridUpper z.re (6 * 2 ^ S))).trans
    (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hre.2 1))
  have hloI := (rationalEncoding_length_le_height (gridLower z.im (6 * 2 ^ S))).trans
    (Nat.mul_le_mul_left 2 (Nat.add_le_add_right him.1 1))
  have hhiI := (rationalEncoding_length_le_height (gridUpper z.im (6 * 2 ^ S))).trans
    (Nat.mul_le_mul_left 2 (Nat.add_le_add_right him.2 1))
  rw [rootEncoding_length]
  dsimp only [gridRectangle]
  omega

/-- The public monic irreducible isolated-root format has polynomial-length
answers on the literal original graph encoding, for every original finite family. -/
theorem public_root_polynomial_bound (w : Wiring) (L : Language) :
    ∃ P : Polynomial ℕ, ∀ G : Instance L,
      ∃ c : RootCode, c.MinimalRepresents (value w L G : ℂ) ∧
        (rootEncoding.encode c).length ≤ P.eval ((inputEncoding L).encode G).length := by
  obtain ⟨A, hA⟩ := fixed_minpoly_height_bound L.fieldPresentation
  obtain ⟨C, hC⟩ := fixed_field_root_separation L.fieldPresentation
  let D := Module.finrank ℚ L.coefficientField
  let M := basisMagnitudeBound L
  let T := (24 * (M + 1)).size
  let BP := coordinateOutputPolynomial w L
  let HP : Polynomial ℕ := Polynomial.C A * (BP + 1)
  let SP : Polynomial ℕ := Polynomial.C 2 * (Polynomial.C C * (BP + 1)) + 1
  let P : Polynomial ℕ :=
    Polynomial.C 2 * (1 + Polynomial.C (D + 1) *
      (Polynomial.C (4 * D.size) + Polynomial.C 4 * (HP + 1) + Polynomial.C 4)) +
      Polynomial.C 14 * (Polynomial.C T + SP + BP + Polynomial.C 2) + Polynomial.C 4
  refine ⟨P, fun G => ?_⟩
  let B := BP.eval ((inputEncoding L).encode G).length
  let v := outputCoordinates w L G
  let z : ℂ := (value w L G : ℂ)
  let p : Polynomial ℚ := minpoly ℚ z
  let S := 2 * (C * (B + 1)) + 1
  let c : RootCode := ⟨densePolynomialCode p, gridRectangle z (6 * 2 ^ S)⟩
  have hv : ∀ i, rationalBitHeight (v i) ≤ B := by
    intro i
    apply Nat.size_le.mpr
    exact max_lt (Nat.size_le.mp (output_coordinate_num_den_bits w L G i).1)
      (Nat.size_le.mp (output_coordinate_num_den_bits w L G i).2)
  let e : L.coefficientField →ₐ[ℚ] ℂ :=
    (algebraicClosure ℚ ℂ).val.comp L.coefficientField.val
  have he : e (L.fieldPresentation.decode v) = z :=
    congrArg (fun a : AlgebraicComplex => (a : ℂ)) (outputCoordinates_spec w L G)
  have heq : minpoly ℚ (L.fieldPresentation.decode v) = p := by
    dsimp only [p]
    rw [← he, minpoly.algHom_eq e e.injective]
  have hi : IsIntegral ℚ z := (value w L G).property
  have hsep : ∀ a : ℂ, Polynomial.aeval a p = 0 → a ≠ z →
      6 / ((6 * 2 ^ S : ℕ) : ℝ) ≤ ‖a - z‖ := by
    intro a ha hne
    have h := hC B v hv z a
    rw [heq] at h
    exact h (minpoly.aeval ℚ z) ha hne
  have hc : c.MinimalRepresents z :=
    grid_minimal_descriptor p z (by positivity) (minpoly.monic hi) (minpoly.irreducible hi)
      (minpoly.aeval ℚ z) hsep
  have hpheight : ∀ j, rationalBitHeight (p.coeff j) ≤ A * (B + 1) := by
    intro j
    rw [← heq]
    exact hA B v hv j
  have hlen := grid_descriptor_length_le p z D (A * (B + 1)) M S B
    (value_minpoly_degree_le w L G) hpheight (value_norm_le w L G)
  refine ⟨c, hc, ?_⟩
  simpa only [P, HP, SP, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_one, c, T, S] using hlen

/-- A real bounded oracle-answer convention exists for every finite language.
Classical selection is used only to package existence, never as an algorithm. -/
theorem boundedAnswers_nonempty (w : Wiring) (L : Language) : Nonempty (BoundedAnswers w L) := by
  obtain ⟨P, hP⟩ := public_root_polynomial_bound w L
  choose answer correct bound using hP
  exact ⟨answer, correct, ⟨P, bound⟩⟩

noncomputable def publicBoundedAnswers (w : Wiring) (L : Language) : BoundedAnswers w L :=
  Classical.choice (boundedAnswers_nonempty w L)

end Paper2.ExactInput
