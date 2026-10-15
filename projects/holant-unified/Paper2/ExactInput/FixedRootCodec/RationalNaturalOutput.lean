import Paper2.ExactInput.FixedRootCodec.ReverseRational

/-! An actual rational-to-natural output program for rational values known to
be natural numbers. It reads the canonical integer numerator and runs the
proved signed-integer-to-natural machine. -/
namespace Paper2.ExactInput.FixedRootCodec.RationalNaturalOutput
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines
noncomputable section

def value (q : ℚ) : ℕ := q.num.toNat

def computes : Computes rationalEncoding encodingNatBool value :=
  RationalArithmetic.numeratorComputes.andThen integerToNatComputes

@[simp] theorem natural_correct (k : ℕ) : value (k : ℚ) = k := by
  simp [value]

theorem correct_of_eq (q : ℚ) (k : ℕ) (h : q = (k : ℚ)) : value q = k := by
  rw [h,natural_correct]

end
end Paper2.ExactInput.FixedRootCodec.RationalNaturalOutput
