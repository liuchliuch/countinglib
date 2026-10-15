import Paper2.ExactInput.Bounds.FixedFamilySize
import Paper2.Complexity.BellMachines.FixedFieldMachines.Semantics
import Paper2.Complexity.BellMachines.RationalArithmetic.Operations

/-! Concrete polynomial-bit-time field arithmetic needed by Bell smoothing.
All scalar programs are the reused canonical rational machines, including gcd
normalization and byte framing. Only the fixed field basis and constants are
selected before graph input. This is a coordinate-code API, not an unproved
conversion from the public isolated-root answer encoding. -/
namespace Paper2.Complexity.BellMachines
open Computability BinaryCompose FixedFieldMachines Paper2.Algebraic
noncomputable section

/-- No scalar arithmetic provider is left as a parameter. -/
def rationalProvider : RationalProvider where
  add := RationalArithmetic.additionComputes
  mul := RationalArithmetic.multiplicationComputes

variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}

/-- The source coordinate codec and the fixed-field codec are literally equal. -/
theorem fieldEncoding_eq (F : FixedField K n) : fieldEncoding F = F.encoding := rfl

def fieldAddition (F : FixedField K n) :
    Computes (pairEncoding F.encoding F.encoding) F.encoding (fun p => p.1 + p.2) :=
  fieldAdditionComputes rationalProvider F

def fieldMultiplication (F : FixedField K n) :
    Computes (pairEncoding F.encoding F.encoding) F.encoding (fun p => p.1 * p.2) :=
  fieldMultiplicationComputes rationalProvider F

def addComputes (F : FixedField K n) {α : Type} {ea : Encoding α Bool}
    {f g : α → K} (u : Computes ea F.encoding f) (v : Computes ea F.encoding g) :
    Computes ea F.encoding (fun x => f x + g x) :=
  congrComputes ((pairComputes u v).andThen (fieldAddition F)) (fun _ => rfl)

def scaleComputes (F : FixedField K n) {α : Type} {ea : Encoding α Bool}
    {f : α → K} (u : Computes ea F.encoding f) (c : K) :
    Computes ea F.encoding (fun x => f x * c) :=
  congrComputes ((pairComputes u (constantComputes ea F.encoding c)).andThen
    (fieldMultiplication F)) (fun _ => rfl)

def subComputes (F : FixedField K n) {α : Type} {ea : Encoding α Bool}
    {f g : α → K} (u : Computes ea F.encoding f) (v : Computes ea F.encoding g) :
    Computes ea F.encoding (fun x => f x - g x) :=
  congrComputes (addComputes F u (scaleComputes F v (-1)))
    (fun x => by simp only [mul_neg_one, sub_eq_add_neg])

/-- Two Y occurrences: query values are supplied in order q14, q13. -/
def twoY (F : FixedField K n) :
    Computes (pairEncoding F.encoding F.encoding) F.encoding
      (fun p => p.1 - p.2) :=
  subComputes F (Wiring.firstComputes _ _) (Wiring.secondComputes _ _)

/-- One Y occurrence paired with a fixed nonzero witness: the sign is the
actual XYX=-Y sign. The inverse of κ is a fixed compiled coefficient. -/
def oneY (F : FixedField K n) (κ : K) :
    Computes (pairEncoding F.encoding F.encoding) F.encoding
      (fun p => -(p.1 - p.2) / κ) :=
  congrComputes (scaleComputes F (twoY F) (-κ⁻¹))
    (fun p => by simp only [div_eq_mul_inv, mul_neg, neg_mul])

abbrev threeAnswerEncoding (F : FixedField K n) :=
  pairEncoding F.encoding (pairEncoding F.encoding F.encoding)

/-- Two I occurrences: query values are supplied in order q13, q14, q12. -/
def twoI (F : FixedField K n) :
    Computes (threeAnswerEncoding F) F.encoding
      (fun p => (p.1 + p.2.1 - p.2.2) / 2) := by
  let q13 := Wiring.firstComputes F.encoding (pairEncoding F.encoding F.encoding)
  let tail := Wiring.secondComputes F.encoding (pairEncoding F.encoding F.encoding)
  let q14 := tail.andThen (Wiring.firstComputes F.encoding F.encoding)
  let q12 := tail.andThen (Wiring.secondComputes F.encoding F.encoding)
  exact congrComputes (scaleComputes F (subComputes F (addComputes F q13 q14) q12) 2⁻¹)
    (fun p => by simp only [Function.comp_def, div_eq_mul_inv])

/-- One I occurrence has zero response; the constant output has a real program. -/
def oneI (F : FixedField K n) {α : Type} (ea : Encoding α Bool) :
    Computes ea F.encoding (fun _ => (0 : K)) := constantComputes ea F.encoding 0

/-- Nonzeroness is required for the mathematical division cancellation. It is
separate from the total finite program, whose constant may also be zero. -/
theorem oneY_cancel (κ y : K) (hκ : κ ≠ 0) : -(-κ * y) / κ = y := by
  rw [neg_mul, neg_neg, mul_div_cancel_left₀ y hκ]

theorem twoY_inFP (F : FixedField K n) :
    InFP (pairEncoding F.encoding F.encoding) F.encoding (fun p => p.1 - p.2) :=
  (twoY F).inFP

theorem oneY_inFP (F : FixedField K n) (κ : K) :
    InFP (pairEncoding F.encoding F.encoding) F.encoding (fun p => -(p.1 - p.2) / κ) :=
  (oneY F κ).inFP

theorem twoI_inFP (F : FixedField K n) :
    InFP (threeAnswerEncoding F) F.encoding (fun p => (p.1 + p.2.1 - p.2.2) / 2) :=
  (twoI F).inFP

end
end Paper2.Complexity.BellMachines
