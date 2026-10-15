import Counting.Algorithm.KarpLubyRequest.ParameterCounts
import Holant.Proofs.LinearProgramming.Support.MachineCombinators.WordCompare

/-!
# Physical bit-budget arithmetic

The input words carry samples, groups, total mass and the complete random tape.
Both physical lengths are computed by actual token-consuming programs. Two H1
binary multiplications and bitwise equality compare the required budget against
the actual tape length. No numeric sample loop runs in this arithmetic stage.
The caller tests zero mass before constructing or calling this stage.
-/
namespace Counting.Algorithm.KarpLubyRequest.TapeBudget.Arithmetic
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing

abbrev WordCompare := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.WordCompare.machine

/-- Count arbitrary physical Boolean tokens, including false bits, with the
canonical H1 carry loop. The semantic length is not an instruction. -/
noncomputable def wordLength : Computes Frame.wordEncoding encodingNatBool List.length where
  machine := UnaryBinary.machine
  time := 2 * Polynomial.X ^ 2 + 5 * Polynomial.X + 4
  outputs word := by
    have first := UnaryBinary.convert_exact word 0
    change UnaryBinary.Runs (UnaryBinary.config 0 word [] [])
      (UnaryBinary.config 3 [] (encodeNat (0 + word.length)) []) _ at first
    rw [Nat.zero_add, UnaryBinary.initial_eq] at first
    have last := UnaryBinary.Runs.one (UnaryBinary.halt_step (encodeNat word.length))
    have run := first.trans last
    have hzero : encodeNat 0 = [] := rfl
    rw [hzero] at run
    refine { steps := 1 + UnaryBinary.ticks [] word.length
             evals_in_steps := run
             steps_le_m := ?_ }
    have hb := UnaryBinary.ticks_le [] word.length
    change _ ≤ (2 * Polynomial.X ^ 2 + 5 * Polynomial.X + 4).eval word.length
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_X, List.length_nil, Nat.zero_add] at *
    nlinarith

/-- Equality is the canonical bitwise comparator, after a literal-codec recode. -/
noncomputable def equal : Computes ParameterCounts.natPair encodingBoolBool
    (fun p => decide (p.1 = p.2)) :=
  recode Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.WordCompare.computes
    (fun p => (encodingNatBool.encode p.1, encodingNatBool.encode p.2))
    (fun _ => rfl) (fun p => by
      change [decide (encodingNatBool.encode p.1 = encodingNatBool.encode p.2)] =
        [decide (p.1 = p.2)]
      simp only [encodingNatBool.encode_injective.eq_iff])

/-- Sample count, group count, total mass, and the unmodified Boolean tape. -/
abbrev Input := ℕ × (ℕ × (ℕ × List Bool))
abbrev massEncoding := pairEncoding encodingNatBool Frame.wordEncoding
abbrev tailEncoding := pairEncoding encodingNatBool massEncoding
abbrev inputEncoding := pairEncoding encodingNatBool tailEncoding

noncomputable def tail : Computes inputEncoding tailEncoding (fun x : Input => x.2) :=
  Wiring.secondComputes encodingNatBool tailEncoding
noncomputable def massTail : Computes inputEncoding massEncoding (fun x : Input => x.2.2) :=
  tail.andThen (Wiring.secondComputes encodingNatBool massEncoding)
noncomputable def samples : Computes inputEncoding encodingNatBool (fun x : Input => x.1) :=
  Wiring.firstComputes encodingNatBool tailEncoding
noncomputable def groups : Computes inputEncoding encodingNatBool (fun x : Input => x.2.1) :=
  tail.andThen (Wiring.firstComputes encodingNatBool massEncoding)
noncomputable def mass : Computes inputEncoding encodingNatBool (fun x : Input => x.2.2.1) :=
  massTail.andThen (Wiring.firstComputes encodingNatBool Frame.wordEncoding)
noncomputable def tape : Computes inputEncoding Frame.wordEncoding (fun x : Input => x.2.2.2) :=
  massTail.andThen (Wiring.secondComputes encodingNatBool Frame.wordEncoding)

/-- The width is counted on the materialized canonical mass word. -/
noncomputable def width : Computes inputEncoding encodingNatBool (fun x : Input => Nat.size x.2.2.1) :=
  mass.andThen ParameterCounts.bitLength
noncomputable def tapeLength : Computes inputEncoding encodingNatBool (fun x : Input => x.2.2.2.length) :=
  tape.andThen wordLength
noncomputable def sampleWidth : Computes inputEncoding encodingNatBool
    (fun x : Input => x.1 * Nat.size x.2.2.1) :=
  (pairComputes samples width).andThen ParameterCounts.multiply
noncomputable def budget : Computes inputEncoding encodingNatBool
    (fun x : Input => x.2.1 * (x.1 * Nat.size x.2.2.1)) :=
  (pairComputes groups sampleWidth).andThen ParameterCounts.multiply

def valid (x : Input) : Bool := decide (x.2.2.2.length = x.2.1 * (x.1 * Nat.size x.2.2.1))

/-- One actual machine, with all projections, retained copies, intermediate
serialization, binary operations and physical comparison included. -/
noncomputable def computes : Computes inputEncoding encodingBoolBool valid :=
  (pairComputes tapeLength budget).andThen equal

theorem input_length (x : Input) :
    (inputEncoding.encode x).length =
      2 * ((encodeNat x.1).length + (encodeNat x.2.1).length +
        (encodeNat x.2.2.1).length) + x.2.2.2.length + 3 := by
  simp only [inputEncoding, tailEncoding, massEncoding, pairEncoding_length]
  change 2 * (encodeNat x.1).length + 1 +
    (2 * (encodeNat x.2.1).length + 1 +
      (2 * (encodeNat x.2.2.1).length + 1 + x.2.2.2.length)) = _
  omega

set_option maxHeartbeats 1000000 in
/-- This bound is polynomial in physical input length even when the numeric
sample or group count is exponentially larger than its encoded word. -/
theorem bit_cost (x : Input) :
    (Primitive.run computes.machine.program (computes.outputs x).steps
      (some (initList computes.machine.computer (inputEncoding.encode x)))).1 ≤
      (ParameterCounts.measuredPolynomial computes).eval (inputEncoding.encode x).length :=
  ParameterCounts.measured_cost computes x

end Counting.Algorithm.KarpLubyRequest.TapeBudget.Arithmetic
