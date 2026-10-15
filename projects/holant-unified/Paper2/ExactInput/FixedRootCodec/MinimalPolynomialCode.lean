import Paper2.ExactInput.FixedRootCodec.MinimalPolynomialProduct
import Paper2.ExactInput.RootOutputSize
import Paper2.Complexity.BellMachines.FixedGadgetSubstitution.Compiler.Lists

/-! The minimal polynomial is emitted as a literal fixed-length sparse rational
coefficient list. Zero high coefficients are permitted by the public polynomial
codec. They do not change its monic irreducible denotation. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity BinaryCompose FixedFieldMachines
open FixedGadgetSubstitution.Compiler Polynomial
noncomputable section
variable {E : Type} [Field E] [Algebra ℚ E] {n : ℕ}

def conjugatePolynomialCode (xs : List (E ≃ₐ[ℚ] E)) (x : E) : RationalPolynomialCode :=
  List.ofFn (fun k : Fin (xs.length+1) =>
    (k.val,rationalProjection ((conjugateProduct xs x).coeff k.val)))

def conjugatePolynomialComputes (F : FixedField E n) (xs : List (E ≃ₐ[ℚ] E)) :
    Computes F.encoding polynomialEncoding (conjugatePolynomialCode xs) := by
  let entry (k : Fin (xs.length+1)) :
      Computes F.encoding (pairEncoding encodingNatBool rationalEncoding)
        (fun x => (k.val,rationalProjection ((conjugateProduct xs x).coeff k.val))) :=
    pairComputes (constantComputes F.encoding encodingNatBool k.val)
      ((coefficientComputes F xs k.val).andThen (rationalProjectionComputes F))
  exact congrComputes (fixedListComputes F.encoding
    (pairEncoding encodingNatBool rationalEncoding)
    (fun x (k : Fin (xs.length+1)) =>
      (k.val,rationalProjection ((conjugateProduct xs x).coeff k.val)))
    entry (List.finRange (xs.length+1))) (fun x => List.ofFn_eq_map.symm)

variable [FiniteDimensional ℚ E] [Normal ℚ E]

def automorphisms : List (E ≃ₐ[ℚ] E) := (Finset.univ : Finset (E ≃ₐ[ℚ] E)).toList

def minimalPolynomialCode (x : E) : RationalPolynomialCode :=
  conjugatePolynomialCode (automorphisms (E := E)) x

def minimalPolynomialComputes (F : FixedField E n) :
    Computes F.encoding polynomialEncoding (minimalPolynomialCode (E := E)) :=
  conjugatePolynomialComputes F automorphisms

theorem minimalPolynomialCode_polynomial (x : E) :
    (minimalPolynomialCode x).polynomial = minpoly ℚ x := by
  have hd : (minpoly ℚ x).natDegree ≤ (automorphisms (E := E)).length := by
    have h := conjugateProduct_natDegree_le (automorphisms (E := E)) x
    rw [automorphisms,conjugateProduct_minpoly,natDegree_map_eq_of_injective
      (algebraMap ℚ E).injective] at h
    exact h
  rw [polynomial_list_sum]
  simp only [minimalPolynomialCode,conjugatePolynomialCode,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,automorphisms,conjugateProduct_minpoly,coeff_map,
    rationalProjection_algebraMap]
  rw [Fin.sum_univ_eq_sum_range (fun i => monomial i ((minpoly ℚ x).coeff i))]
  exact ((minpoly ℚ x).as_sum_range' _ (Nat.lt_succ_of_le hd)).symm

end
end Paper2.ExactInput.FixedRootCodec
