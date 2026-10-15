import Paper2.ExactInput.FixedRootCodec.ReverseDense
import Paper2.ExactInput.FixedRootCodec.ReverseContains

/-! Exact candidate verification for the strict public root descriptor.
Both the polynomial and the candidate are runtime inputs. The degree bound
is fixed before execution; evaluation uses the real rational arithmetic
programs and the fixed field's proved multiplication table. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}

def fieldPower (F : FixedField K n) : ℕ → (Fin n → ℚ) → (Fin n → ℚ)
  | 0, _ => F.unitCode
  | m+1, v => F.mulCode (fieldPower F m v) v

def fieldPowerComputes (F : FixedField K n) : (m : ℕ) →
    Computes (vectorEncoding n) (vectorEncoding n) (fieldPower F m)
  | 0 => constantComputes (vectorEncoding n) (vectorEncoding n) F.unitCode
  | m+1 => congrComputes
      ((pairComputes (fieldPowerComputes F m) (identityComputes (vectorEncoding n))).andThen
        (multiplicationComputes BellMachines.rationalProvider F.toArithmeticData))
      (fun _ => rfl)

theorem fieldPower_value (F : FixedField K n) (m : ℕ) (v : Fin n → ℚ) :
    F.decode (fieldPower F m v)=(F.decode v)^m := by
  induction m with
  | zero => simp [fieldPower]
  | succ m hm => simp [fieldPower,hm,pow_succ]

def fieldPolynomialValue (F : FixedField K n) {N : ℕ}
    (c : Fin N → ℚ) (v : Fin n → ℚ) : Fin n → ℚ :=
  ∑ i : Fin N, c i • fieldPower F i.val v

def fieldPolynomialComputes (F : FixedField K n) (N : ℕ) :
    Computes (pairEncoding (vectorEncoding N) (vectorEncoding n)) (vectorEncoding n)
      (fun p => fieldPolynomialValue F p.1 p.2) := by
  let ec := pairEncoding (vectorEncoding N) (vectorEncoding n)
  let c := Wiring.firstComputes (vectorEncoding N) (vectorEncoding n)
  let v := Wiring.secondComputes (vectorEncoding N) (vectorEncoding n)
  apply assembleComputes
  intro j
  apply congrComputes (BellMachines.rationalProvider.sumComputes ec N
    (fun p i => p.1 i*fieldPower F i.val p.2 j) (fun i =>
      BellMachines.rationalProvider.mulComputes
        (c.andThen (coordinateComputes N i))
        ((v.andThen (fieldPowerComputes F i.val)).andThen (coordinateComputes n j))))
  intro p
  simp [fieldPolynomialValue,Finset.sum_apply]

theorem fieldPolynomialValue_value (F : FixedField K n) {N : ℕ}
    (c : Fin N → ℚ) (v : Fin n → ℚ) :
    F.decode (fieldPolynomialValue F c v)=
      Polynomial.aeval (F.decode v) (VariablePolynomial.polynomial c) := by
  simp only [fieldPolynomialValue,map_sum,map_smul,fieldPower_value]
  simp [VariablePolynomial.polynomial,Polynomial.aeval_def,Algebra.smul_def]

def fieldPolynomialZeroComputes (F : FixedField K n) (N : ℕ) :
    Computes (pairEncoding (vectorEncoding N) (vectorEncoding n)) encodingBoolBool
      (fun p => decide (Polynomial.aeval (F.decode p.2)
        (VariablePolynomial.polynomial p.1)=0)) := by
  apply congrComputes ((fieldPolynomialComputes F N).andThen (zeroComputes (vectorEncoding n)))
  intro p
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply,decide_eq_true_eq]
  exact (F.decode.injective.eq_iff (a := fieldPolynomialValue F p.1 p.2) (b := 0)).symm.trans
    (by simp only [map_zero,fieldPolynomialValue_value])

def rootRectangleComputes : Computes rootEncoding rectangleEncoding RootCode.rectangle :=
  recode (Wiring.secondComputes polynomialEncoding rectangleEncoding)
    (fun c => (c.coefficients,c.rectangle)) (fun _ => rfl) (fun _ => rfl)

def fieldRootCandidate (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) (N : ℕ)
    (c : RootCode) (v : Fin n → ℚ) : Bool :=
  decide (Polynomial.aeval (F.decode v) (VariablePolynomial.polynomial
    (denseCoefficients N c.coefficients))=0) && decide (c.rectangle.Contains (e (F.decode v)))

def fieldRootCandidateComputes (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) (N : ℕ) :
    Computes (pairEncoding rootEncoding (vectorEncoding n)) encodingBoolBool
      (fun p => fieldRootCandidate F e N p.1 p.2) := by
  let c := Wiring.firstComputes rootEncoding (vectorEncoding n)
  let v := Wiring.secondComputes rootEncoding (vectorEncoding n)
  let hp := (pairComputes (c.andThen (denseRootCoefficientsComputes N)) v).andThen
    (fieldPolynomialZeroComputes F N)
  let hr := (pairComputes v (c.andThen rootRectangleComputes)).andThen
    (fieldRectangleContainsComputes F e)
  exact congrComputes (boolAndComputes hp hr) (fun _ => rfl)

theorem fieldRootCandidate_iff (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) (N : ℕ)
    (c : RootCode) (v : Fin n → ℚ) (hd : c.polynomial.natDegree<N) :
    fieldRootCandidate F e N c v=true ↔
      Polynomial.aeval (e (F.decode v)) c.polynomial=0 ∧ c.rectangle.Contains (e (F.decode v)) := by
  rw [fieldRootCandidate,Bool.and_eq_true]
  simp only [decide_eq_true_eq,denseRootCoefficients_polynomial N c hd]
  have hz : Polynomial.aeval (F.decode v) c.polynomial=0 ↔
      Polynomial.aeval (e (F.decode v)) c.polynomial=0 := by
    rw [Polynomial.aeval_algHom_apply e (F.decode v) c.polynomial]
    have hinj : Function.Injective e := fun _ _ h => e.injective h
    simpa only [map_zero] using
      (hinj.eq_iff (a := Polynomial.aeval (F.decode v) c.polynomial) (b := 0)).symm
  exact and_congr_left (fun _ => hz)

theorem fieldRootCandidate_correct (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) (N : ℕ)
    (c : RootCode) (x : K) (h : c.MinimalRepresents (e x))
    (hd : c.polynomial.natDegree<N) (v : Fin n → ℚ) :
    fieldRootCandidate F e N c v=true ↔ F.decode v=x := by
  rw [fieldRootCandidate_iff F e N c v hd]
  constructor
  · intro hv
    exact e.injective (h.1.2.2.2 _ hv.2 hv.1)
  · intro hv
    rw [hv]
    exact ⟨h.1.2.2.1,h.1.2.1⟩

end
end Paper2.ExactInput.FixedRootCodec
