import Paper2.ExactInput.FixedRootCodec.MinimalPolynomialField
import Paper2.ExactInput.FixedRootCodec.IsolatingRectangle

/-! The complete strict output codec for a fixed embedded number field.
A genuine finite conjugate circuit emits the monic irreducible minimal
polynomial, and genuine bisection/interval circuits emit its open isolating
rectangle. Physical wiring serializes the public RootCode bytes. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity Polynomial
open BinaryCompose FixedFieldMachines
noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] {n : ℕ}

def coordinateRootCode (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) (v : Fin n → ℚ) : RootCode :=
  ⟨coordinateMinimalPolynomialCode F e v,(fieldRectangleCodec F e).rectangle v⟩

def coordinateRootComputes (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) :
    Computes (vectorEncoding n) rootEncoding (coordinateRootCode F e) :=
  recode (pairComputes (coordinateMinimalPolynomialComputes F e)
    (fieldRectangleCodec F e).computes) id (fun _ => rfl) (fun _ => rfl)

theorem coordinateRootCode_correct (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) (v : Fin n → ℚ) :
    (coordinateRootCode F e v).MinimalRepresents (e (F.decode v)) := by
  have ha : IsIntegral ℚ (F.decode v) :=
    ⟨fixedAnnihilator F v,fixedAnnihilator_monic F v,
      by simpa only [Polynomial.aeval_def] using fixedAnnihilator_aeval F v⟩
  have he : IsIntegral ℚ (e (F.decode v)) := ha.map e
  have hp : (coordinateRootCode F e v).polynomial = minpoly ℚ (e (F.decode v)) :=
    coordinateMinimalPolynomialCode_polynomial F e v
  refine ⟨⟨?_,(fieldRectangleCodec F e).contains v,?_,?_⟩,?_,?_⟩
  · rw [hp]
    exact minpoly.ne_zero he
  · rw [hp]
    exact minpoly.aeval ℚ (e (F.decode v))
  · intro w hw hr
    apply (fieldRectangleCodec F e).isolates v w hw
    rw [hp,minpoly.algHom_eq e e.injective] at hr
    exact hr
  · rw [hp]
    exact minpoly.monic he
  · rw [hp]
    exact minpoly.irreducible he

def fieldRootCode (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) (x : K) : RootCode :=
  coordinateRootCode F e (F.decode.symm x)

def fieldRootComputes (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) :
    Computes F.encoding rootEncoding (fieldRootCode F e) :=
  recode (coordinateRootComputes F e) F.decode.symm (fun _ => rfl) (fun _ => rfl)

theorem fieldRootCode_correct (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) (x : K) :
    (fieldRootCode F e x).MinimalRepresents (e x) := by
  simpa only [fieldRootCode,F.decode.apply_symm_apply] using
    coordinateRootCode_correct F e (F.decode.symm x)

end
end Paper2.ExactInput.FixedRootCodec
