import Paper2.ExactInput.CoordinateOutputBound
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.Algebra.Polynomial.Degree.Support

/-! Concrete public descriptor size accounting. Degree and raw-byte framing are
proved here; quantitative coefficient heights and root separation are still separate
mathematical obligations, rather than assumed public-output certificates. -/
namespace Paper2.ExactInput
open Computability Paper2.Algebraic Paper2.Complexity Paper2.Problem Polynomial

/-- Dense coefficient lists avoid redundant sparse terms in a chosen public answer. -/
noncomputable def densePolynomialCode (p : ℚ[X]) : RationalPolynomialCode :=
  List.ofFn (fun i : Fin (p.natDegree + 1) => (i.val, p.coeff i.val))

theorem polynomial_list_sum (c : RationalPolynomialCode) :
    c.polynomial = (c.map (fun t => monomial t.1 t.2)).sum := by
  induction c with
  | nil => rfl
  | cons t c ih => simp [RationalPolynomialCode.polynomial, ih]

@[simp] theorem densePolynomialCode_polynomial (p : ℚ[X]) :
    (densePolynomialCode p).polynomial = p := by
  rw [polynomial_list_sum]
  simp only [densePolynomialCode, List.map_ofFn, List.sum_ofFn]
  dsimp only [Function.comp_def]
  rw [Fin.sum_univ_eq_sum_range (fun i => monomial i (p.coeff i))]
  exact p.as_sum_range.symm

@[simp] theorem densePolynomialCode_length (p : ℚ[X]) :
    (densePolynomialCode p).length = p.natDegree + 1 := List.length_ofFn

/-- The raw polynomial byte length is exact, including all term delimiters. -/
theorem framedList_length {A : Type} (e : Encoding A Bool) (xs : List A) :
    ((framedListEncoding e).encode xs).length =
      1 + (xs.map (fun a => 2 * (e.encode a).length + 2)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (framedListEncode e (a :: xs)).length = _
    change (framedListEncode e xs).length = _ at ih
    simp only [framedListEncode, List.length_cons, List.length_append, frame_length,
      List.map_cons, List.sum_cons]
    omega

theorem polynomialEncoding_length (c : RationalPolynomialCode) :
    (polynomialEncoding.encode c).length =
      1 + (c.map (fun t => 4 * t.1.size + 2 * (rationalEncoding.encode t.2).length + 4)).sum := by
  rw [polynomialEncoding, framedList_length]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  simp only [framedProductEncoding_length, encodingNatBool, encodeNat_length]
  omega

theorem rectangleEncoding_length (r : RationalRectangle) :
    (rectangleEncoding.encode r).length =
      2 * (rationalEncoding.encode r.reLower).length +
      2 * (rationalEncoding.encode r.reUpper).length +
      2 * (rationalEncoding.encode r.imLower).length +
      (rationalEncoding.encode r.imUpper).length + 3 := by
  change ((framedProductEncoding rationalEncoding (framedProductEncoding rationalEncoding
    (framedProductEncoding rationalEncoding rationalEncoding))).encode
      (r.reLower, r.reUpper, r.imLower, r.imUpper)).length = _
  simp only [framedProductEncoding_length]
  omega

/-- Root choice is encoded by four rational endpoints, with no hidden root index.
This is the exact byte length of the same parser used by the problem definition. -/
theorem rootEncoding_length (c : RootCode) :
    (rootEncoding.encode c).length =
      2 * (polynomialEncoding.encode c.coefficients).length +
      2 * (rationalEncoding.encode c.rectangle.reLower).length +
      2 * (rationalEncoding.encode c.rectangle.reUpper).length +
      2 * (rationalEncoding.encode c.rectangle.imLower).length +
      (rationalEncoding.encode c.rectangle.imUpper).length + 4 := by
  change ((framedProductEncoding polynomialEncoding rectangleEncoding).encode
    (c.coefficients, c.rectangle)).length = _
  rw [framedProductEncoding_length, rectangleEncoding_length]
  dsimp only
  omega

/-- Embedding the derived number field in ℂ does not change the minimal polynomial. -/
theorem value_minpoly_degree_le (w : Wiring) (L : Language) (G : Instance L) :
    (minpoly ℚ (value w L G : ℂ)).natDegree ≤ Module.finrank ℚ L.coefficientField := by
  let embedding : L.coefficientField →ₐ[ℚ] ℂ :=
    (algebraicClosure ℚ ℂ).val.comp L.coefficientField.val
  have hvalue : embedding ((fieldNetwork w L G).denote Fin.elim0) = (value w L G : ℂ) :=
    congrArg (fun z : Paper2.Tractable.AlgebraicComplex => (z : ℂ)) (fieldNetwork_value w L G)
  rw [← hvalue, minpoly.algHom_eq embedding embedding.injective]
  exact minpoly.natDegree_le _

/-- Every answer admits a nonredundant strict minimal descriptor with at most
fixed-field-degree plus one polynomial entries. No rectangle size bound is smuggled in. -/
theorem dense_public_output_exists (w : Wiring) (L : Language) (G : Instance L) :
    ∃ c : RootCode, c.MinimalRepresents (value w L G : ℂ) ∧
      c.coefficients.length ≤ Module.finrank ℚ L.coefficientField + 1 := by
  obtain ⟨c, hc⟩ := RootCode.minimal_coverage (value w L G)
  let d : RootCode := ⟨densePolynomialCode c.polynomial, c.rectangle⟩
  have hp : d.polynomial = c.polynomial := densePolynomialCode_polynomial _
  have hd : d.MinimalRepresents (value w L G : ℂ) := by
    rcases hc with ⟨⟨hn, hb, hr, hu⟩, hm, hi⟩
    exact ⟨⟨by simpa [hp] using hn, hb, by simpa [hp] using hr,
      fun z hz hroot => hu z hz (by simpa [hp] using hroot)⟩,
      by simpa [hp] using hm, by simpa [hp] using hi⟩
  refine ⟨d, hd, ?_⟩
  change (densePolynomialCode c.polynomial).length ≤ _
  rw [densePolynomialCode_length, RootCode.minimalRepresents_polynomial hc]
  exact Nat.add_le_add_right (value_minpoly_degree_le w L G) 1

end Paper2.ExactInput
