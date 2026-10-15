import Holant.Complexity.RationalArithmetic.Normalization
import Counting.Algorithm.KarpLubyMachine.NumeratorMedian
import Counting.Computation.PolyTime

/-!
# Reusing the canonical finite fraction-normalization machine

H1 supplies the unique source of the binary gcd/division/normalization machines.
The machine below is that same 14-stack Boolean machine. Its input and output
codecs remain H1's component codecs: the output is a framed pair of integer
parity-code and denominator bits. It is not R1's signed/framed rational codec.

The client theorem connects the executable natural-only R1 median to this machine and
bounds its transitions by R1's proved numerator/denominator bit sizes. Executing the natural-only
selector on machine stacks and converting the normalized pair
to R1's final output codec remain separate, explicitly unproved bridges.
-/
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

namespace Counting.Algorithm.KarpLubyMachine.FractionNormalization

open Counting.Algorithm.KarpLuby
open Turing Computability

abbrev inputEncoding := Holant.Complexity.RationalArithmetic.fractionEncoding
abbrev componentEncoding := Holant.Complexity.BinaryArithmetic.EncodedAddition.inputEncoding
abbrev computer := Holant.Complexity.RationalArithmetic.Normalization.computer

/-- Canonical numerator integer-code and denominator, in the upstream exact codec. -/
def components (q : ℚ) : ℕ × ℕ := (Equiv.intEquivNat q.num, q.den)

/-- The same existing finite machine, with its all-internal-alphabets certificate. -/
noncomputable def polyTime : Counting.Computation.PolyTime inputEncoding componentEncoding
    (fun p : ℤ × ℕ => components (mkRat p.1 p.2)) :=
  Holant.Complexity.RationalArithmetic.Normalization.computes.toPolyTime

/-- The input has only linear overhead over ordinary numerator/denominator sizes. -/
theorem input_length_le (a s : ℕ) :
    (inputEncoding.encode ((a : ℤ), s)).length ≤ 2 * a.size + s.size + 3 := by
  rw [Holant.Complexity.RationalArithmetic.fractionEncoding_length]
  change 2 * (encodeNat (Equiv.intEquivNat (a : ℤ))).length + (encodeNat s).length + 1 ≤ _
  rw [Holant.Algebraic.encodeNat_length, Holant.Algebraic.encodeNat_length]
  have h := Holant.Algebraic.intCode_size_le (a : ℤ)
  simp only [Int.natAbs_natCast] at h
  omega

/-- No gcd or division operation is assumed atomic: this is the actual finite
machine's proved transition budget, including copying and cleanup. -/
noncomputable def outputs (a s : ℕ) :
    TM2OutputsInTime computer (inputEncoding.encode ((a : ℤ), s))
      (some (componentEncoding.encode (components ((a : ℚ) / s))))
      (200 * (2 * a.size + s.size + 4) ^ 3) := by
  have r : TM2OutputsInTime computer (inputEncoding.encode ((a : ℤ), s))
      (some (componentEncoding.encode (components ((a : ℚ) / s))))
      (200 * ((inputEncoding.encode ((a : ℤ), s)).length + 1) ^ 3) := by
    simpa [Holant.Complexity.RationalArithmetic.Normalization.computes,
      components, Rat.mkRat_eq_div] using
      Holant.Complexity.RationalArithmetic.Normalization.computes.outputs ((a : ℤ), s)
  refine { steps := r.steps, evals_in_steps := r.evals_in_steps, steps_le_m := ?_ }
  refine r.steps_le_m.trans ?_
  have hl := input_length_le a s
  exact Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (by omega) 3)

private def retargetRun {tm : FinTM2} {input : List (tm.Γ tm.k₀)}
    {old new : Option (List (tm.Γ tm.k₁))} {t u : ℕ}
    (r : TM2OutputsInTime tm input old t) (hout : old = new) (ht : t ≤ u) :
    TM2OutputsInTime tm input new u := by
  subst new
  exact { steps := r.steps, evals_in_steps := r.evals_in_steps, steps_le_m := r.steps_le_m.trans ht }

/-- The normalizer's actual input is produced by the natural-only median
program, so this contract does not merely assert that some suitable fraction exists. -/
noncomputable def estimatorOutputs {n : ℕ} (cs : List (DNF.Clause n)) (s g : ℕ)
    (tape : CoinTape (Program.randomBitBudget cs s g)) :
    TM2OutputsInTime computer
      (inputEncoding.encode (((NumeratorMedian.estimate cs s g tape).value : ℤ), s))
      (some (componentEncoding.encode (components (Program.estimate cs s g tape))))
      (200 * (3 * s.size + 2 * cs.length.size + 2 * n + 8) ^ 3) := by
  have ha := NumeratorMedian.estimate_size_le cs s g tape
  have ht : 200 * (2 * (NumeratorMedian.estimate cs s g tape).value.size + s.size + 4) ^ 3 ≤
      200 * (3 * s.size + 2 * cs.length.size + 2 * n + 8) ^ 3 :=
    Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (by omega) 3)
  exact retargetRun (outputs (NumeratorMedian.estimate cs s g tape).value s)
    (congrArg (fun q : ℚ => some (componentEncoding.encode (components q)))
      (NumeratorMedian.estimate_refines cs s g tape).symm) ht

/-- A request-specific true transition bound in the original encoded parameter
sizes. This is the normalization stage only, not a bound for its caller. -/
noncomputable def requestOutputs {n : ℕ} (f : DNF.Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    TM2OutputsInTime computer
      (inputEncoding.encode
        (((NumeratorMedian.estimate (DNF.normalizeFormula f)
          (Program.requestedSamples (DNF.normalizeFormula f) epsilon)
          (Program.requestedGroups delta) tape).value : ℤ),
          Program.requestedSamples (DNF.normalizeFormula f) epsilon))
      (some (componentEncoding.encode (components (Program.run f epsilon delta tape))))
      (200 * (5 * f.length.size + 6 * epsilon.den.size + 2 * n + 38) ^ 3) := by
  have hs := ResourceBounds.samples_size_le (DNF.normalizeFormula f).length epsilon
  have hm := Nat.size_le_size (ResourceBounds.normalized_length_le f)
  have r := estimatorOutputs (DNF.normalizeFormula f)
    (Program.requestedSamples (DNF.normalizeFormula f) epsilon) (Program.requestedGroups delta) tape
  have ht : 200 * (3 * (Program.requestedSamples (DNF.normalizeFormula f) epsilon).size +
      2 * (DNF.normalizeFormula f).length.size + 2 * n + 8) ^ 3 ≤
      200 * (5 * f.length.size + 6 * epsilon.den.size + 2 * n + 38) ^ 3 := by
    apply Nat.mul_le_mul_left 200
    apply Nat.pow_le_pow_left _ 3
    unfold Program.requestedSamples
    omega
  have he : Program.run f epsilon delta tape = Program.estimate (DNF.normalizeFormula f)
      (Program.requestedSamples (DNF.normalizeFormula f) epsilon) (Program.requestedGroups delta) tape := rfl
  exact retargetRun r
    (congrArg (fun q : ℚ => some (componentEncoding.encode (components q))) he.symm) ht

/-- Structural finiteness and bounded statement syntax are inherited unchanged. -/
theorem stack_count : Fintype.card computer.K = 14 :=
  Holant.Complexity.RationalArithmetic.Normalization.stack_count

theorem label_count : Fintype.card computer.Λ = 58 :=
  Holant.Complexity.RationalArithmetic.Normalization.label_count

theorem state_count : Fintype.card computer.σ = 72 :=
  Holant.Complexity.RationalArithmetic.Normalization.state_count

theorem primitive_budget (label : computer.Λ) :
    Holant.Complexity.TM2Cost.budget (computer.m label) ≤ 12 :=
  Holant.Complexity.RationalArithmetic.Normalization.program_budget label

end Counting.Algorithm.KarpLubyMachine.FractionNormalization
