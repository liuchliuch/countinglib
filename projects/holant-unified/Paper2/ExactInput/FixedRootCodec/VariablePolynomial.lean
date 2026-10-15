import Paper2.ExactInput.FixedRootCodec.PolynomialMachines
import Holant.Complexity.RationalArithmetic.Inverse

/-! Variable rational coefficient vectors of a fixed maximum degree. Every
coefficient and evaluation point is runtime input; only the vector dimension
is fixed before execution. This is the arithmetic layer for exact root
refinement, including a genuine total rational reciprocal program. -/
namespace Paper2.ExactInput.FixedRootCodec.VariablePolynomial
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines Polynomial
noncomputable section

def polynomial {n : ℕ} (v : Fin n → ℚ) : ℚ[X] :=
  ∑ i : Fin n, monomial i.val (v i)

def evaluation {n : ℕ} (v : Fin n → ℚ) (q : ℚ) : ℚ :=
  ∑ i : Fin n, v i * q ^ i.val

theorem evaluation_eq {n : ℕ} (v : Fin n → ℚ) (q : ℚ) :
    evaluation v q = (polynomial v).eval q := by
  simp [evaluation,polynomial,Polynomial.eval_finsetSum]

theorem coefficient_eq {n : ℕ} (v : Fin n → ℚ) (k : ℕ) :
    (polynomial v).coeff k = if h : k < n then v ⟨k,h⟩ else 0 := by
  classical
  by_cases h : k < n
  · simp only [h,dite_true]
    rw [polynomial,finsetSum_coeff,Finset.sum_eq_single (⟨k,h⟩ : Fin n)]
    · simp
    · intro i _ hi
      have hv : i.val ≠ k := fun he => hi (Fin.ext he)
      simp [coeff_monomial,hv]
    · simp
  · simp only [h,dite_false]
    rw [polynomial,finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro i _
    have hv : i.val ≠ k := by intro he; exact h (he ▸ i.isLt)
    simp [coeff_monomial,hv]

def inputEncoding (n : ℕ) := pairEncoding (vectorEncoding n) rationalEncoding

def coefficientComputes (n : ℕ) (i : Fin n) :
    Computes (inputEncoding n) rationalEncoding (fun p => p.1 i) :=
  congrComputes ((Wiring.firstComputes _ _).andThen (coordinateComputes n i))
    (fun _ => rfl)

def pointComputes (n : ℕ) :
    Computes (inputEncoding n) rationalEncoding (fun p => p.2) :=
  Wiring.secondComputes _ _

def evaluationComputes (n : ℕ) :
    Computes (inputEncoding n) rationalEncoding (fun p => evaluation p.1 p.2) :=
  rationalProvider.sumComputes (inputEncoding n) n _ (fun i =>
    rationalProvider.mulComputes (coefficientComputes n i)
      ((pointComputes n).andThen (rationalPowerComputes i.val)))

def negativeComputes (n : ℕ) :
    Computes (inputEncoding n) encodingBoolBool
      (fun p => decide (evaluation p.1 p.2 < 0)) :=
  congrComputes ((evaluationComputes n).andThen rationalNegativeComputes) (fun _ => rfl)

def zeroComputes (n : ℕ) :
    Computes (inputEncoding n) encodingBoolBool
      (fun p => decide (evaluation p.1 p.2 = 0)) :=
  congrComputes ((evaluationComputes n).andThen
    (FixedRootCodec.zeroComputes rationalEncoding)) (fun _ => rfl)

def reciprocalComputes : Computes rationalEncoding rationalEncoding (fun q : ℚ => q⁻¹) :=
  recode (TractableAlgorithms.Paper1Machine.computes
    Holant.Complexity.RationalArithmetic.inverseComputes) id
    (fun _ => rfl) (fun _ => rfl)

def divisionComputes :
    Computes (pairEncoding rationalEncoding rationalEncoding) rationalEncoding
      (fun p : ℚ × ℚ => p.1 / p.2) :=
  congrComputes (rationalProvider.mulComputes (Wiring.firstComputes _ _)
    ((Wiring.secondComputes _ _).andThen reciprocalComputes))
      (fun p => (div_eq_mul_inv p.1 p.2).symm)

def derivative {n : ℕ} (v : Fin n → ℚ) (i : Fin n) : ℚ :=
  if h : i.val+1 < n then (i.val+1 : ℚ) * v ⟨i.val+1,h⟩ else 0

def derivativeComputes (n : ℕ) :
    Computes (vectorEncoding n) (vectorEncoding n) (derivative (n := n)) := by
  apply assembleComputes
  intro i
  by_cases h : i.val+1 < n
  · exact congrComputes (rationalProvider.mulComputes
      (constantComputes (vectorEncoding n) rationalEncoding (i.val+1 : ℚ))
      (coordinateComputes n ⟨i.val+1,h⟩)) (fun v => by simp [derivative,h])
  · exact congrComputes (constantComputes (vectorEncoding n) rationalEncoding 0)
      (fun v => by simp [derivative,h])

theorem derivative_polynomial {n : ℕ} (v : Fin n → ℚ) :
    polynomial (derivative v) = (polynomial v).derivative := by
  ext k
  rw [coefficient_eq,coeff_derivative,coefficient_eq]
  by_cases h : k < n
  · simp only [h,dite_true]
    change (if h' : k+1<n then (k+1 : ℚ) * v ⟨k+1,h'⟩ else 0) = _
    by_cases h' : k+1<n <;> simp [h',mul_comm]
  · have h' : ¬k+1<n := by omega
    simp [h,h']

end
end Paper2.ExactInput.FixedRootCodec.VariablePolynomial
