import Paper2.ExactInput.FixedRootCodec.MinimalPolynomialCode
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Every fixed embedded number field is enlarged once to its finite normal
closure. The enlargement, its basis and every conjugate linear map are fixed
before input coordinates. The running converter is a fixed rational matrix
followed by the already checked finite conjugate circuit. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity BinaryCompose FixedFieldMachines
open Polynomial
noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] {n : ℕ}

def NormalField (K : Type) [Field K] [Algebra ℚ K] :=
  IntermediateField.normalClosure ℚ K ℂ

instance : FiniteDimensional ℚ (NormalField K) :=
  normalClosure.is_finiteDimensional ℚ K ℂ

instance : Normal ℚ (NormalField K) := by
  let : IsNormalClosure ℚ K (NormalField K) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure
      (fun x : K => IsAlgClosed.splits ((minpoly ℚ x).map (algebraMap ℚ ℂ)))
  exact IsNormalClosure.normal (F := ℚ) (K := K) (L := NormalField K)

def normalEmbed (e : K →ₐ[ℚ] ℂ) : K →ₐ[ℚ] NormalField K :=
  e.codRestrict _ (fun x => e.fieldRange_le_normalClosure ⟨x,rfl⟩)

omit [FiniteDimensional ℚ K] in
@[simp] theorem normalEmbed_coe (e : K →ₐ[ℚ] ℂ) (x : K) :
    (normalEmbed e x : ℂ) = e x := rfl

def normalPresentation : FixedField (NormalField K) (Module.finrank ℚ (NormalField K)) :=
  FixedField.ofFiniteDimensional (NormalField K)

def normalCoordinates (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) :
    (Fin n → ℚ) →ₗ[ℚ] (Fin (Module.finrank ℚ (NormalField K)) → ℚ) :=
  (normalPresentation (K := K)).decode.symm.toLinearMap.comp
    ((normalEmbed e).toLinearMap.comp F.decode.toLinearMap)

def normalCoordinatesComputes (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) :
    Computes F.encoding (normalPresentation (K := K)).encoding (normalEmbed e) :=
  recode (Paper2.FixedFieldOutput.linearComputes (normalCoordinates F e)) F.decode.symm
    (fun _ => rfl) (fun x => by
      change (vectorEncoding _).encode ((normalPresentation (K := K)).decode.symm
        (normalEmbed e (F.decode (F.decode.symm x)))) = _
      rw [F.decode.apply_symm_apply]
      rfl)

def fieldMinimalPolynomialCode (e : K →ₐ[ℚ] ℂ) (x : K) : RationalPolynomialCode :=
  minimalPolynomialCode (normalEmbed e x)

def fieldMinimalPolynomialComputes (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) :
    Computes F.encoding polynomialEncoding (fieldMinimalPolynomialCode e) :=
  (normalCoordinatesComputes F e).andThen
    (minimalPolynomialComputes (normalPresentation (K := K)))

theorem fieldMinimalPolynomialCode_polynomial (e : K →ₐ[ℚ] ℂ) (x : K) :
    (fieldMinimalPolynomialCode e x).polynomial = minpoly ℚ (e x) := by
  rw [fieldMinimalPolynomialCode,minimalPolynomialCode_polynomial]
  rw [minpoly.algHom_eq (normalEmbed e) (normalEmbed e).injective,
    minpoly.algHom_eq e e.injective]

def coordinateMinimalPolynomialCode (F : FixedField K n) (e : K →ₐ[ℚ] ℂ)
    (v : Fin n → ℚ) : RationalPolynomialCode := fieldMinimalPolynomialCode e (F.decode v)

def coordinateMinimalPolynomialComputes (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) :
    Computes (vectorEncoding n) polynomialEncoding (coordinateMinimalPolynomialCode F e) :=
  recode (fieldMinimalPolynomialComputes F e) F.decode
    (fun v => by change (vectorEncoding n).encode (F.decode.symm (F.decode v)) = _
                 rw [F.decode.symm_apply_apply]) (fun _ => rfl)

theorem coordinateMinimalPolynomialCode_polynomial (F : FixedField K n)
    (e : K →ₐ[ℚ] ℂ) (v : Fin n → ℚ) :
    (coordinateMinimalPolynomialCode F e v).polynomial = minpoly ℚ (e (F.decode v)) :=
  fieldMinimalPolynomialCode_polynomial e _

end
end Paper2.ExactInput.FixedRootCodec
