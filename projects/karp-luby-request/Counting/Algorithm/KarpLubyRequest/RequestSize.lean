import Counting.Algorithm.KarpLubyRequest.Contract
import Counting.Algorithm.KarpLubyRequest.ParameterSemantics
import Counting.Algorithm.KarpLuby.EncodedBounds
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Physical request length and approximation parameters

`requestLength` counts the canonical formula and rational parameters, including
their three outer frames, but excludes the random tape. `wholeLength` also
counts every random bit consumed by the original estimator. The original
`reciprocalCeiling` is the strict integer upper approximation `floor(1/ε)+1`,
including at integral reciprocals; this module does not replace that convention.

These bounds permit substitution into a future whole-machine polynomial in the
physical input length. They neither construct that machine nor assert its cost.
The confidence contribution is charged by its rational encoding length.
-/
namespace Counting.Algorithm.KarpLubyRequest.RequestSize
open Counting.Algorithm.KarpLuby
open DNF

variable {n : ℕ}

/-- Deterministic canonical request prefix, with all three outer frames. -/
def requestLength (f : Formula n) (epsilon delta : ℚ) : ℕ :=
  2 * (formulaBitLength f + (Encoding.encodeOutput epsilon).length +
    (Encoding.encodeOutput delta).length) + 3

/-- The complete canonical request, including the actual finite random tape. -/
def wholeLength (f : Formula n) (epsilon delta : ℚ) : ℕ :=
  requestLength f epsilon delta + Program.requestedBudget f epsilon delta

theorem encodeRun_length (f : Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    (ProgramEncoding.encodeRun f epsilon delta tape).length =
      wholeLength f epsilon delta := by
  unfold ProgramEncoding.encodeRun
  rw [Contract.request_encode]
  simp only [Contract.join, Contract.encodedFields, ProgramEncoding.ofRun,
    List.length_append, Encoding.frame_length, List.length_ofFn]
  change 2 * formulaBitLength f + 1 +
    (2 * (Encoding.encodeOutput epsilon).length + 1) +
    (2 * (Encoding.encodeOutput delta).length + 1) +
    Program.requestedBudget f epsilon delta = _
  unfold wholeLength requestLength
  omega

/-- The length budget uses the original sample, group and width expressions. -/
theorem wholeLength_stages (f : Formula n) (epsilon delta : ℚ) :
    wholeLength f epsilon delta = requestLength f epsilon delta +
      Program.requestedGroups delta *
        (Program.requestedSamples (normalizeFormula f) epsilon *
          dyadicBits (Program.totalMass (normalizeFormula f))) := rfl

/-- Zero mass has width zero and therefore no random-tape contribution. -/
theorem wholeLength_zero_mass (f : Formula n) (epsilon delta : ℚ)
    (hm : Program.totalMass (normalizeFormula f) = 0) :
    wholeLength f epsilon delta = requestLength f epsilon delta := by
  rw [wholeLength_stages, hm]
  simp [dyadicBits]

theorem formula_le_requestLength (f : Formula n) (epsilon delta : ℚ) :
    formulaBitLength f ≤ requestLength f epsilon delta := by
  unfold requestLength
  omega

theorem denominator_le_requestLength (f : Formula n) (epsilon delta : ℚ) :
    delta.den.size ≤ requestLength f epsilon delta := by
  have hd : delta.den.size ≤ (Encoding.encodeOutput delta).length := by
    rw [Encoding.output_length, Encoding.nat_length]
    omega
  unfold requestLength
  omega

/-- This bound contains no random-tape length on its right-hand side. -/
theorem budget_le_requestLength (f : Formula n) (epsilon delta : ℚ) :
    Program.requestedBudget f epsilon delta ≤
      288 * (requestLength f epsilon delta + 2) * requestLength f epsilon delta *
        reciprocalCeiling epsilon ^ 2 * (2 * requestLength f epsilon delta + 1) := by
  refine (requestedBudget_le_formula_bits f epsilon delta).trans ?_
  have hf := formula_le_requestLength f epsilon delta
  have hd := denominator_le_requestLength f epsilon delta
  gcongr

theorem wholeLength_le (f : Formula n) (epsilon delta : ℚ) :
    wholeLength f epsilon delta ≤
      requestLength f epsilon delta +
        288 * (requestLength f epsilon delta + 2) * requestLength f epsilon delta *
          reciprocalCeiling epsilon ^ 2 * (2 * requestLength f epsilon delta + 1) :=
  Nat.add_le_add_left (budget_le_requestLength f epsilon delta) _

/-- Positive accuracy replaces the exact integer adapter by its inverse bound. -/
theorem wholeLength_le_inverse (f : Formula n) {epsilon : ℚ} (he : 0 < epsilon)
    (delta : ℚ) :
    (wholeLength f epsilon delta : ℚ) ≤
      (requestLength f epsilon delta : ℚ) +
        288 * ((requestLength f epsilon delta : ℚ) + 2) *
          (requestLength f epsilon delta : ℚ) * (1 / epsilon + 1) ^ 2 *
            (2 * (requestLength f epsilon delta : ℚ) + 1) := by
  have hb : (wholeLength f epsilon delta : ℚ) ≤
      (requestLength f epsilon delta : ℚ) +
        288 * ((requestLength f epsilon delta : ℚ) + 2) *
          (requestLength f epsilon delta : ℚ) * (reciprocalCeiling epsilon : ℚ) ^ 2 *
            (2 * (requestLength f epsilon delta : ℚ) + 1) := by
    exact_mod_cast wholeLength_le f epsilon delta
  refine hb.trans ?_
  have hr := reciprocalCeiling_le_inv_add_one he
  gcongr

/-- A single polynomial for composition with a physical-input machine bound. -/
noncomputable def boundPolynomial : Polynomial ℕ :=
  Polynomial.X + 288 * (Polynomial.X + 2) * Polynomial.X * Polynomial.X ^ 2 *
    (2 * Polynomial.X + 1)

theorem boundPolynomial_eval (N : ℕ) :
    boundPolynomial.eval N = N + 288 * (N + 2) * N * N ^ 2 * (2 * N + 1) := by
  simp [boundPolynomial]

/-- The deterministic input length and numerical inverse-accuracy adapter are
the only arguments of this polynomial; no hidden tape-size argument remains. -/
theorem wholeLength_le_polynomial (f : Formula n) (epsilon delta : ℚ) :
    wholeLength f epsilon delta ≤
      boundPolynomial.eval (requestLength f epsilon delta + reciprocalCeiling epsilon) := by
  refine (wholeLength_le f epsilon delta).trans ?_
  rw [boundPolynomial_eval]
  gcongr <;> omega

/-- The same bound can use positive raw rational components directly. -/
theorem wholeLength_raw_accuracy (f : Formula n) (e : RationalFields.Fields) (delta : ℚ)
    (he : e.denominator ≠ []) (hu : ParameterSemantics.unsigned e) :
    wholeLength f (RationalFields.value e) delta ≤
      boundPolynomial.eval (requestLength f (RationalFields.value e) delta +
        (Computability.decodeNat e.denominator / Computability.decodeNat e.magnitude + 1)) := by
  simpa only [ParameterSemantics.reciprocal_raw e he hu] using
    wholeLength_le_polynomial f (RationalFields.value e) delta

end Counting.Algorithm.KarpLubyRequest.RequestSize
