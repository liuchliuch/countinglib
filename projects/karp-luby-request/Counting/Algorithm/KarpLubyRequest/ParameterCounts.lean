import Counting.Algorithm.KarpLubyRequest.ParameterSemantics
import Holant.Complexity.BinaryCompose.Arithmetic
import Holant.Complexity.BinaryArithmetic.EncodedDivision
import Holant.Complexity.FixedFieldMachines.LeftMap
import Holant.Complexity.FixedFieldMachines.Reverse
import Holant.Complexity.FixedFieldMachines.Constant
import Holant.Complexity.GraphPreprocessing.UnaryBinary

/-!
# Actual binary machines for sample and group parameters

Every combinator below constructs a finite Boolean-stack program. Quotient,
addition, multiplication, reversal, copying, framing and ordered transfer are
canonical H1 providers. The bit-length machine is the original token-counting
program on the physical canonical word, not an opcode for `Nat.size`.

The input is five canonical natural words: epsilon numerator/denominator,
delta numerator/denominator, and the supplied normalized clause count. This
module proves computation of the binary counts. Materializing and executing
that many samples is a separate numerical-accuracy runtime obligation.
-/
namespace Counting.Algorithm.KarpLubyRequest.ParameterCounts
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Counting.Algorithm.KarpLuby

abbrev natPair := pairEncoding encodingNatBool encodingNatBool

/-- The original serialized arithmetic inputs use reversed component words.
Both reversals and pair framing are actual finite machines. -/
noncomputable def arithmeticInput :
    Computes natPair BinaryArithmetic.EncodedAddition.inputEncoding id :=
  recode (pairComputes
    ((Wiring.firstComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool))
    ((Wiring.secondComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool)))
    id (fun _ => rfl) (fun _ => rfl)

abbrev quotientMachine : Machine where
  K := (BinaryArithmetic.EncodedDivision.computer false).K
  input := (BinaryArithmetic.EncodedDivision.computer false).k₀
  output := (BinaryArithmetic.EncodedDivision.computer false).k₁
  Label := (BinaryArithmetic.EncodedDivision.computer false).Λ
  main := (BinaryArithmetic.EncodedDivision.computer false).main
  State := (BinaryArithmetic.EncodedDivision.computer false).σ
  initial := (BinaryArithmetic.EncodedDivision.computer false).initialState
  program := (BinaryArithmetic.EncodedDivision.computer false).m

noncomputable def quotientReversed :
    Computes BinaryArithmetic.EncodedDivision.inputEncoding encodingNatBool (fun p => p.1 / p.2) where
  machine := quotientMachine
  time := BinaryArithmetic.EncodedDivision.divisionPolyTime.time
  outputs p := by
    have h := BinaryArithmetic.EncodedDivision.divisionPolyTime.outputsFun p
    change TM2OutputsInTime quotientMachine.computer
      (List.map id (BinaryArithmetic.EncodedDivision.inputEncoding.encode p))
      (some (List.map id (encodeNat (p.1 / p.2)))) _ at h
    change TM2OutputsInTime quotientMachine.computer
      (BinaryArithmetic.EncodedDivision.inputEncoding.encode p)
      (some (encodeNat (p.1 / p.2))) _
    simpa only [List.map_id] using h

noncomputable def quotient : Computes natPair encodingNatBool (fun p => p.1 / p.2) :=
  arithmeticInput.andThen quotientReversed

noncomputable def add : Computes natPair encodingNatBool (fun p => p.1 + p.2) :=
  arithmeticInput.andThen additionComputes

noncomputable def multiply : Computes natPair encodingNatBool (fun p => p.1 * p.2) :=
  arithmeticInput.andThen multiplicationComputes

noncomputable def increment : Computes encodingNatBool encodingNatBool (fun n => n + 1) :=
  (pairComputes (identityComputes encodingNatBool)
    (constantComputes encodingNatBool encodingNatBool 1)).andThen add

/-- Count actual bits of a canonical natural using H1's physical token loop.
The token values may be either Boolean value; only token consumption matters. -/
noncomputable def bitLength : Computes encodingNatBool encodingNatBool Nat.size where
  machine := UnaryBinary.machine
  time := 2 * Polynomial.X ^ 2 + 5 * Polynomial.X + 4
  outputs n := by
    have first := UnaryBinary.convert_exact (encodeNat n) 0
    change UnaryBinary.Runs (UnaryBinary.config 0 (encodeNat n) [] [])
      (UnaryBinary.config 3 [] (encodeNat (0 + (encodeNat n).length)) []) _ at first
    rw [Nat.zero_add, Holant.Algebraic.encodeNat_length] at first
    rw [UnaryBinary.initial_eq] at first
    have last := UnaryBinary.Runs.one (UnaryBinary.halt_step (encodeNat n.size))
    have run := first.trans last
    have hzero : encodeNat 0 = [] := rfl
    rw [hzero] at run
    refine { steps := 1 + UnaryBinary.ticks [] (encodeNat n).length
             evals_in_steps := by
               change UnaryBinary.Runs (initList UnaryBinary.machine.computer (encodeNat n))
                 (haltList UnaryBinary.machine.computer (encodeNat n.size))
                 (1 + UnaryBinary.ticks [] (encodeNat n).length)
               simpa only [Holant.Algebraic.encodeNat_length] using run
             steps_le_m := ?_ }
    have hb := UnaryBinary.ticks_le [] (encodeNat n).length
    change _ ≤ (2 * Polynomial.X ^ 2 + 5 * Polynomial.X + 4).eval (encodeNat n).length
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_X, List.length_nil, Nat.zero_add] at *
    nlinarith

/-- Explicit field data, with the fifth count supplied by actual normalization. -/
abbrev Input := ℕ × (ℕ × (ℕ × (ℕ × ℕ)))
abbrev tailEncoding := pairEncoding encodingNatBool (pairEncoding encodingNatBool encodingNatBool)
abbrev restEncoding := pairEncoding encodingNatBool tailEncoding
abbrev inputEncoding := pairEncoding encodingNatBool restEncoding
abbrev outputEncoding := pairEncoding encodingNatBool
  (pairEncoding encodingNatBool (pairEncoding encodingNatBool encodingNatBool))

noncomputable def rest : Computes inputEncoding restEncoding (fun x : Input => x.2) :=
  Wiring.secondComputes encodingNatBool restEncoding
noncomputable def tail : Computes inputEncoding tailEncoding (fun x : Input => x.2.2) :=
  rest.andThen (Wiring.secondComputes encodingNatBool tailEncoding)
noncomputable def lastPair : Computes inputEncoding natPair (fun x : Input => x.2.2.2) :=
  tail.andThen (Wiring.secondComputes encodingNatBool natPair)

noncomputable def epsilonNumerator : Computes inputEncoding encodingNatBool (fun x : Input => x.1) :=
  Wiring.firstComputes encodingNatBool restEncoding
noncomputable def epsilonDenominator : Computes inputEncoding encodingNatBool (fun x : Input => x.2.1) :=
  rest.andThen (Wiring.firstComputes encodingNatBool tailEncoding)
noncomputable def deltaNumerator : Computes inputEncoding encodingNatBool (fun x : Input => x.2.2.1) :=
  tail.andThen (Wiring.firstComputes encodingNatBool natPair)
noncomputable def deltaDenominator : Computes inputEncoding encodingNatBool (fun x : Input => x.2.2.2.1) :=
  lastPair.andThen (Wiring.firstComputes encodingNatBool encodingNatBool)
noncomputable def clauses : Computes inputEncoding encodingNatBool (fun x : Input => x.2.2.2.2) :=
  lastPair.andThen (Wiring.secondComputes encodingNatBool encodingNatBool)

noncomputable def epsilonReciprocal : Computes inputEncoding encodingNatBool
    (fun x : Input => x.2.1 / x.1 + 1) :=
  ((pairComputes epsilonDenominator epsilonNumerator).andThen quotient).andThen increment
noncomputable def deltaReciprocal : Computes inputEncoding encodingNatBool
    (fun x : Input => x.2.2.2.1 / x.2.2.1 + 1) :=
  ((pairComputes deltaDenominator deltaNumerator).andThen quotient).andThen increment

noncomputable def reciprocalSquare : Computes inputEncoding encodingNatBool
    (fun x : Input => (x.2.1 / x.1 + 1) ^ 2) :=
  congrComputes ((pairComputes epsilonReciprocal epsilonReciprocal).andThen multiply)
    (fun _ => (pow_two _).symm)

noncomputable def sampleCount : Computes inputEncoding encodingNatBool
    (fun x : Input => 144 * x.2.2.2.2 * (x.2.1 / x.1 + 1) ^ 2) :=
  (pairComputes
    ((pairComputes (constantComputes inputEncoding encodingNatBool 144) clauses).andThen multiply)
    reciprocalSquare).andThen multiply

noncomputable def groupCount : Computes inputEncoding encodingNatBool
    (fun x : Input => 2 * (Nat.size (x.2.2.2.1 / x.2.2.1 + 1) + 1)) :=
  ((deltaReciprocal.andThen bitLength).andThen increment).andThen doublingComputes

def result (x : Input) : ℕ × (ℕ × (ℕ × ℕ)) :=
  (x.2.1 / x.1 + 1, x.2.2.2.1 / x.2.2.1 + 1,
    144 * x.2.2.2.2 * (x.2.1 / x.1 + 1) ^ 2,
    2 * (Nat.size (x.2.2.2.1 / x.2.2.1 + 1) + 1))

/-- One actual finite program produces both reciprocal counts, the sample
count, and the group count. Pairing and every intermediate transfer are charged. -/
noncomputable def computes : Computes inputEncoding outputEncoding result :=
  pairComputes epsilonReciprocal (pairComputes deltaReciprocal (pairComputes sampleCount groupCount))

def fields (e d : RationalFields.Fields) (m : ℕ) : Input :=
  (decodeNat e.magnitude, decodeNat e.denominator,
    decodeNat d.magnitude, decodeNat d.denominator, m)

/-- The binary outputs are exactly R1's existing numerical budgets on positive
raw rational fields, even when those raw fields are noncanonical. -/
theorem result_fields (e d : RationalFields.Fields) (m : ℕ)
    (he : e.denominator ≠ []) (hd : d.denominator ≠ [])
    (hue : ParameterSemantics.unsigned e) (hud : ParameterSemantics.unsigned d) :
    result (fields e d m) =
      (reciprocalCeiling (RationalFields.value e), reciprocalCeiling (RationalFields.value d),
        samples m (RationalFields.value e), Program.requestedGroups (RationalFields.value d)) := by
  rw [ParameterSemantics.reciprocal_raw e he hue, ParameterSemantics.reciprocal_raw d hd hud]
  change (_, _, _, _) = (_, _, 144 * m * reciprocalCeiling (RationalFields.value e) ^ 2,
    2 * (Nat.size (reciprocalCeiling (RationalFields.value d)) + 1))
  rw [ParameterSemantics.reciprocal_raw e he hue, ParameterSemantics.reciprocal_raw d hd hud]
  rfl

/-- Physical input length, with the existing forward pair codec made explicit. -/
theorem input_length (x : Input) :
    (inputEncoding.encode x).length =
      2 * ((encodeNat x.1).length + (encodeNat x.2.1).length +
        (encodeNat x.2.2.1).length + (encodeNat x.2.2.2.1).length) +
        (encodeNat x.2.2.2.2).length + 4 := by
  simp only [inputEncoding, restEncoding, tailEncoding, pairEncoding_length]
  change 2 * (encodeNat x.1).length + 1 +
    (2 * (encodeNat x.2.1).length + 1 +
      (2 * (encodeNat x.2.2.1).length + 1 +
        (2 * (encodeNat x.2.2.2.1).length + 1 + (encodeNat x.2.2.2.2).length))) = _
  omega

/-- Primitive bound for the exact interpreter used by the caller bank. -/
noncomputable def measuredPolynomial {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (w : Computes ea eb f) : Polynomial ℕ :=
  Polynomial.C w.machine.primitiveBudget * w.time

theorem measured_cost {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (w : Computes ea eb f) (x : A) :
    (Primitive.run w.machine.program (w.outputs x).steps
      (some (initList w.machine.computer (ea.encode x)))).1 ≤
      (measuredPolynomial w).eval (ea.encode x).length := by
  have hr : (fun c => c.bind w.machine.computer.step)^[(w.outputs x).steps]
      (some (initList w.machine.computer (ea.encode x))) =
      some (haltList w.machine.computer (eb.encode (f x))) := (w.outputs x).evals_in_steps
  have hc := Primitive.execution_cost w.machine.program w.machine.primitiveBudget
    w.machine.program_budget_le (w.outputs x).steps _ _ hr
  have hb := Nat.mul_le_mul_left w.machine.primitiveBudget (w.outputs x).steps_le_m
  simpa only [measuredPolynomial, Polynomial.eval_mul, Polynomial.eval_C] using hc.2.trans hb

set_option maxHeartbeats 1000000 in
/-- Real primitive cost of the compiled arithmetic program. This is polynomial
in the binary input length; it is not the cost of drawing all requested samples. -/
theorem primitive_cost (x : Input) :
    (Primitive.run computes.machine.program (computes.outputs x).steps
      (some (initList computes.machine.computer (inputEncoding.encode x)))).1 ≤
      (measuredPolynomial computes).eval (inputEncoding.encode x).length :=
  measured_cost computes x

end Counting.Algorithm.KarpLubyRequest.ParameterCounts
