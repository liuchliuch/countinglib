import Paper2.ExactInput.FixedRootCodec.ReverseDenominator
import Holant.Proofs.CountingMachines.AnswerDecoder.IntegerToNat

/-! Exact reverse decoding for rational and natural oracle values. It uses the
constant coefficient of the monic minimal polynomial, so every correct public
descriptor is accepted, irrespective of its rectangle or sparse term order.
This theorem has an explicit rational-value premise; it does not provide a
general number-field root decoder. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines
noncomputable section
set_option backward.isDefEq.respectTransparency false

def rootCoefficientsComputes : Computes rootEncoding polynomialEncoding RootCode.coefficients :=
  recode (Wiring.firstComputes polynomialEncoding rectangleEncoding)
    (fun c => (c.coefficients,c.rectangle)) (fun _ => rfl) (fun _ => rfl)

def rationalRootValue (c : RootCode) : ℚ := -sparseCoefficient 0 c.coefficients

def rationalRootComputes : Computes rootEncoding rationalEncoding rationalRootValue :=
  congrComputes (rationalProvider.mulComputes
    (constantComputes rootEncoding rationalEncoding (-1))
    (rootCoefficientsComputes.andThen (sparseCoefficientComputes 0)))
    (fun c => by simp [rationalRootValue])

theorem rationalRootValue_correct (c : RootCode) (q : ℚ)
    (h : c.MinimalRepresents (q : ℂ)) : rationalRootValue c=q := by
  unfold rationalRootValue
  rw [sparseCoefficient_polynomial]
  change -c.polynomial.coeff 0=q
  rw [RootCode.minimalRepresents_polynomial h]
  have hp : minpoly ℚ (q : ℂ)=Polynomial.X-Polynomial.C q := minpoly.eq_X_sub_C ℂ q
  rw [hp]
  simp

def naturalRootValue (c : RootCode) : ℕ := (rationalRootValue c).num.toNat

def integerToNatComputes : Computes IntegerArithmetic.encoding encodingNatBool Int.toNat :=
  recode (TractableAlgorithms.Paper1Machine.computes
    Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.IntegerToNat.computes)
    id (fun _ => rfl) (fun _ => rfl)

def naturalRootComputes : Computes rootEncoding encodingNatBool naturalRootValue :=
  congrComputes ((rationalRootComputes.andThen RationalArithmetic.numeratorComputes).andThen
    integerToNatComputes) (fun _ => rfl)

theorem naturalRootValue_correct (c : RootCode) (m : ℕ)
    (h : c.MinimalRepresents (m : ℂ)) : naturalRootValue c=m := by
  unfold naturalRootValue
  have hq : c.MinimalRepresents ((m : ℚ) : ℂ) := by simpa using h
  rw [rationalRootValue_correct c (m : ℚ) hq]
  simp

variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}

def rationalCastCoordinatesComputes (F : Holant.Algebraic.FixedField K n) :
    Computes rationalEncoding (vectorEncoding n) (fun q : ℚ => q • F.unitCode) :=
  congrComputes (assembleComputes rationalEncoding n (fun q i => q*F.unitCode i)
    (fun i => rationalProvider.mulComputes (identityComputes rationalEncoding)
      (constantComputes rationalEncoding rationalEncoding (F.unitCode i))))
    (fun q => by funext i; simp only [Pi.smul_apply,smul_eq_mul])

theorem rationalCast_coordinates (F : Holant.Algebraic.FixedField K n) (q : ℚ) :
    F.decode.symm (algebraMap ℚ K q)=q • F.unitCode := by
  apply F.decode.injective
  rw [LinearEquiv.apply_symm_apply,F.decode.map_smul,Holant.Algebraic.FixedField.decode_unit]
  simp [Algebra.smul_def]

def rationalCastFieldComputes (F : Holant.Algebraic.FixedField K n) :
    Computes rationalEncoding F.encoding (algebraMap ℚ K) :=
  recode (rationalCastCoordinatesComputes F) id (fun _ => rfl)
    (fun q => by
      rw [← TractableAlgorithms.Paper1Machine.vector_bytes_eq]
      change (Holant.Algebraic.vectorEncoding n).encode (q • F.unitCode)=
        (Holant.Algebraic.vectorEncoding n).encode (F.decode.symm (algebraMap ℚ K q))
      rw [rationalCast_coordinates])

/-- This reverse field program is valid for rational outputs of any fixed
number field. The unrestricted algebraic case needs additional root recovery. -/
def rationalRootFieldComputes (F : Holant.Algebraic.FixedField K n) :
    Computes rootEncoding F.encoding (fun c => algebraMap ℚ K (rationalRootValue c)) :=
  rationalRootComputes.andThen (rationalCastFieldComputes F)

theorem rationalRootField_correct (F : Holant.Algebraic.FixedField K n)
    (e : K →ₐ[ℚ] ℂ) (c : RootCode) (q : ℚ)
    (h : c.MinimalRepresents (q : ℂ)) :
    e (algebraMap ℚ K (rationalRootValue c))=(q : ℂ) := by
  rw [rationalRootValue_correct c q h]
  exact e.commutes q

end
end Paper2.ExactInput.FixedRootCodec
