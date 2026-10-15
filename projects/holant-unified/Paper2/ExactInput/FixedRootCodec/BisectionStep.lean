import Paper2.ExactInput.FixedRootCodec.PolynomialMachines

/-! One genuine fixed-polynomial bisection round. A shared integer denominator
is doubled each round, so exact midpoint arithmetic does not introduce an
exponential growth of rational denominator bit lengths. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines
noncomputable section

abbrev BisectionState := ℤ × ℤ × ℕ

def bisectionEncoding : Encoding BisectionState Bool :=
  pairEncoding IntegerArithmetic.encoding
    (pairEncoding IntegerArithmetic.encoding encodingNatBool)

def leftComputes : Computes bisectionEncoding IntegerArithmetic.encoding
    (fun s => s.1) := Wiring.firstComputes _ _

def rightComputes : Computes bisectionEncoding IntegerArithmetic.encoding
    (fun s => s.2.1) :=
  congrComputes ((Wiring.secondComputes _ _).andThen (Wiring.firstComputes _ _)) (fun _ => rfl)

def denominatorComputes : Computes bisectionEncoding encodingNatBool
    (fun s => s.2.2) :=
  congrComputes ((Wiring.secondComputes _ _).andThen (Wiring.secondComputes _ _)) (fun _ => rfl)

def sumComputes : Computes bisectionEncoding IntegerArithmetic.encoding
    (fun s => s.1 + s.2.1) :=
  congrComputes ((pairComputes leftComputes rightComputes).andThen
    RationalArithmetic.integerAdditionComputes) (fun _ => rfl)

def doubleLeftComputes : Computes bisectionEncoding IntegerArithmetic.encoding
    (fun s => s.1 + s.1) :=
  congrComputes ((pairComputes leftComputes leftComputes).andThen
    RationalArithmetic.integerAdditionComputes) (fun _ => rfl)

def doubleRightComputes : Computes bisectionEncoding IntegerArithmetic.encoding
    (fun s => s.2.1 + s.2.1) :=
  congrComputes ((pairComputes rightComputes rightComputes).andThen
    RationalArithmetic.integerAdditionComputes) (fun _ => rfl)

def doubleDenominatorComputes : Computes bisectionEncoding encodingNatBool
    (fun s => 2 * s.2.2) :=
  congrComputes ((pairComputes (constantComputes bisectionEncoding encodingNatBool 2)
    denominatorComputes).andThen RationalArithmetic.naturalMultiplicationComputes) (fun _ => rfl)

def midpoint (s : BisectionState) : ℚ := mkRat (s.1 + s.2.1) (2 * s.2.2)

def midpointComputes : Computes bisectionEncoding rationalEncoding midpoint :=
  congrComputes ((pairComputes sumComputes doubleDenominatorComputes).andThen
    RationalArithmetic.normalizationForwardComputes) (fun _ => rfl)

def bisect (p : RationalPolynomialCode) (s : BisectionState) : BisectionState :=
  if RationalPolynomialCode.evalRational (midpoint s) p = 0 then
    (s.1 + s.2.1,s.1 + s.2.1,2 * s.2.2)
  else if RationalPolynomialCode.evalRational (midpoint s) p < 0 then
    (s.1 + s.2.1,s.2.1 + s.2.1,2 * s.2.2)
  else (s.1 + s.1,s.1 + s.2.1,2 * s.2.2)

def bisectionStepComputes (p : RationalPolynomialCode) :
    Computes bisectionEncoding bisectionEncoding (bisect p) := by
  let equalCase := pairComputes sumComputes (pairComputes sumComputes doubleDenominatorComputes)
  let lower := pairComputes sumComputes (pairComputes doubleRightComputes doubleDenominatorComputes)
  let upper := pairComputes doubleLeftComputes (pairComputes sumComputes doubleDenominatorComputes)
  let negative := congrComputes (midpointComputes.andThen (polynomialNegativeComputes p))
    (fun _ => rfl)
  let zero := congrComputes (midpointComputes.andThen (polynomialZeroComputes p))
    (fun _ => rfl)
  exact congrComputes (ifComputes zero equalCase (ifComputes negative lower upper))
    (fun s => by simp only [bisect,Function.comp_apply,decide_eq_true_eq])

@[simp] theorem bisect_denominator (p : RationalPolynomialCode) (s : BisectionState) :
    (bisect p s).2.2 = 2 * s.2.2 := by
  unfold bisect
  split_ifs <;> rfl

theorem bisect_abs_bound (p : RationalPolynomialCode) (s : BisectionState) (M : ℕ)
    (hl : s.1.natAbs ≤ M) (hu : s.2.1.natAbs ≤ M) :
    (bisect p s).1.natAbs ≤ 2 * M ∧ (bisect p s).2.1.natAbs ≤ 2 * M := by
  have hsum := (Int.natAbs_add_le s.1 s.2.1).trans (Nat.add_le_add hl hu)
  have hleft := (Int.natAbs_add_le s.1 s.1).trans (Nat.add_le_add hl hl)
  have hright := (Int.natAbs_add_le s.2.1 s.2.1).trans (Nat.add_le_add hu hu)
  unfold bisect
  split_ifs <;> simp only <;> constructor <;> omega

theorem bisection_denominator (p : RationalPolynomialCode) (s : BisectionState) (k : ℕ) :
    ((bisect p)^[k] s).2.2 = 2 ^ k * s.2.2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',bisect_denominator,ih,pow_succ]
    ring

theorem bisection_abs_bound (p : RationalPolynomialCode) (s : BisectionState)
    (M : ℕ) (hl : s.1.natAbs ≤ M) (hu : s.2.1.natAbs ≤ M) (k : ℕ) :
    ((bisect p)^[k] s).1.natAbs ≤ 2 ^ k * M ∧
      ((bisect p)^[k] s).2.1.natAbs ≤ 2 ^ k * M := by
  induction k with
  | zero => simpa using And.intro hl hu
  | succ k ih =>
    have h := bisect_abs_bound p ((bisect p)^[k] s) (2 ^ k * M) ih.1 ih.2
    simpa only [Function.iterate_succ_apply',pow_succ,Nat.mul_assoc,Nat.mul_comm,
      Nat.mul_left_comm] using h

end
end Paper2.ExactInput.FixedRootCodec
