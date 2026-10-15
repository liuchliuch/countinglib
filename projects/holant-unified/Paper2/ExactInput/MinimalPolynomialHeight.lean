import Paper2.ExactInput.MonicDivisorHeight
import Paper2.ExactInput.RootOutputSize

/-! The strict minimal polynomial, not only an annihilator, of every original
Holant answer has polynomially bounded rational coefficient sizes. -/
namespace Paper2.ExactInput
open Paper2.Algebraic Paper2.Tractable Paper2.Problem Polynomial

theorem fixed_minpoly_height_bound {K : Type*} [Field K] [Algebra ℚ K]
    {n : ℕ} (F : FixedField K n) :
    ∃ C : ℕ, ∀ (B : ℕ) (v : Fin n → ℚ), (∀ i, rationalBitHeight (v i) ≤ B) →
      ∀ j, rationalBitHeight ((minpoly ℚ (F.decode v)).coeff j) ≤ C * (B + 1) := by
  obtain ⟨A, hA⟩ := fixedAnnihilator_height_bound F
  refine ⟨n + (n + 1).size + (n + 2) * A + 2, fun B v hv j => ?_⟩
  have ha : IsIntegral ℚ (F.decode v) :=
    ⟨fixedAnnihilator F v, fixedAnnihilator_monic F v, fixedAnnihilator_aeval F v⟩
  have h := monic_divisor_height_bound n (A * (B + 1))
    (fixedAnnihilator_natDegree F v).le (fixedAnnihilator_monic F v).ne_zero
    (hA B v hv) (minpoly.monic ha)
    (minpoly.dvd ℚ (F.decode v) (fixedAnnihilator_aeval F v)) j
  nlinarith

theorem output_minpoly_polynomial_bound (w : Wiring) (L : Language) :
    ∃ P : Polynomial ℕ, ∀ G : Instance L, ∀ j,
      rationalBitHeight ((minpoly ℚ (value w L G : ℂ)).coeff j) ≤
        P.eval ((inputEncoding L).encode G).length := by
  obtain ⟨C, hC⟩ := fixed_minpoly_height_bound L.fieldPresentation
  refine ⟨Polynomial.C C * (coordinateOutputPolynomial w L + 1), fun G j => ?_⟩
  let e : L.coefficientField →ₐ[ℚ] ℂ :=
    (algebraicClosure ℚ ℂ).val.comp L.coefficientField.val
  have he : e (L.fieldPresentation.decode (outputCoordinates w L G)) = (value w L G : ℂ) :=
    congrArg (fun z : AlgebraicComplex => (z : ℂ)) (outputCoordinates_spec w L G)
  rw [← he, minpoly.algHom_eq e e.injective]
  have h := hC ((coordinateOutputPolynomial w L).eval ((inputEncoding L).encode G).length)
    (outputCoordinates w L G) (fun i => ?_) j
  · simpa using h
  · apply Nat.size_le.mpr
    exact max_lt (Nat.size_le.mp (output_coordinate_num_den_bits w L G i).1)
      (Nat.size_le.mp (output_coordinate_num_den_bits w L G i).2)

end Paper2.ExactInput
