import Counting.Algorithm.KarpLuby.ProgramEncoding
import Counting.Algorithm.KarpLuby.Program

/-!
# Executable boundary and overlap examples

Only these tiny test fixtures enumerate all *dyadic words*, to check the exact
finite average. The production estimator samples words from its supplied tape
and never enumerates assignments or the dyadic support.
-/

namespace Counting.Algorithm.KarpLuby.Examples

open DNF Program

/-- `x₀ ∨ x₀ ∨ (x₁ ∧ ¬x₁) ∨ x₁`, with a third variable absent from every term. -/
def overlapping : Formula 3 :=
  [[(0, true)], [(0, true)], [(1, true), (1, false)], [(1, true)]]

/-- The empty term is true, even when surrounded by a contradictory term. -/
def tautology : Formula 3 := [[], [(2, true), (2, false)]]

def contradiction : Formula 3 := [[(0, true), (0, false)]]

def noTerms : Formula 3 := []

def nullaryTrue : Formula 0 := [[]]

/-- Exhaustive tiny-support diagnostic, not the implementation of the estimator. -/
def trialTable {n : ℕ} (f : Formula n) : List ℕ :=
  let cs := normalizeFormula f
  (List.range (dyadicSize (totalMass cs))).map (trial cs)

/-- A deterministic diagnostic average over the finite support. -/
def supportAverage {n : ℕ} (f : Formula n) : ℚ :=
  ((trialTable f).sum : ℚ) / (trialTable f).length

example : (normalizeFormula overlapping).length = 3 := by decide
example : totalMass (normalizeFormula overlapping) = 12 := by decide
example : trialTable overlapping =
    [16, 16, 16, 16, 0, 0, 0, 0, 16, 0, 16, 0, 0, 0, 0, 0] := by decide
example : supportAverage overlapping = 6 := by
  change (96 : ℚ) / 16 = 6
  norm_num
example : supportAverage tautology = 8 := by
  change (128 : ℚ) / 16 = 8
  norm_num
example : supportAverage contradiction = 0 := by
  change (0 : ℚ) / 1 = 0
  norm_num
example : supportAverage noTerms = 0 := by
  change (0 : ℚ) / 1 = 0
  norm_num
example : supportAverage nullaryTrue = 1 := by
  change (2 : ℚ) / 2 = 1
  norm_num

/-- Both 16-word blocks visit words 0 through 15, using most-significant-bit decoding. -/
def overlappingTape : CoinTape (randomBitBudget (normalizeFormula overlapping) 16 2) :=
  fun i => decide (((i.val / 4) / 2 ^ (3 - i.val % 4)) % 2 = 1)

/-- Full prefix selection, assignment unranking, ownership, mean, and median pipeline. -/
def overlappingEstimate : ℚ :=
  estimate (normalizeFormula overlapping) 16 2 overlappingTape

/-- A real rational-parameter execution on a fixed tape with equally many 0 and 8 words. -/
def tautologyRun : ℚ :=
  run tautology (1 / 2) (1 / 4)
    (fun i => decide (i.val % 4 = 0 ∧ (i.val / 4) % 2 = 1))

/-- The zero-mass branch requires no tape coordinates. -/
example : requestedBudget contradiction (1 / 2) (1 / 4) = 0 := by decide

/-- Rational output is encoded explicitly as integer numerator and positive denominator. -/
def encodedTautology : ℤ × ℕ := encodeOutput tautologyRun

/-- Input framing preserves the full explicit syntax, including contradictory terms. -/
def overlappingInput : Encoding.Input := ⟨3, overlapping⟩

def inputRoundtrip : Option (ℕ × ℕ) :=
  (Encoding.decodeInput (Encoding.encodeInput overlappingInput)).map
    fun x => (x.variableCount, x.formula.length)

example : Encoding.decodeOutput (Encoding.encodeOutput (7 / 12)) = some (7 / 12) :=
  Encoding.decode_encodeOutput _

example : Encoding.decodeOutput (Encoding.encodeOutput (-5 / 9)) = some (-5 / 9) :=
  Encoding.decode_encodeOutput _

example : Encoding.decodeOutput ((Encoding.prod Encoding.int Encoding.nat).encode (7, 0)) = none :=
  Encoding.output_decode_zero_denominator _

end Counting.Algorithm.KarpLuby.Examples

/-- Standalone executable diagnostics for the bounded-tape implementation. -/
def main : IO Unit := do
  let ns := "Counting.Algorithm.KarpLuby"
  let overlap := Counting.Algorithm.KarpLuby.Examples.overlappingEstimate
  let exact := Counting.Algorithm.KarpLuby.Examples.tautologyRun
  unless overlap == 6 do throw (IO.userError "two-group pipeline returned an incorrect value")
  unless exact == 8 do throw (IO.userError "rational request pipeline returned an incorrect value")
  let serialized := Counting.Algorithm.KarpLuby.Encoding.decodeOutput
    (Counting.Algorithm.KarpLuby.ProgramEncoding.evalBits
      (Counting.Algorithm.KarpLuby.ProgramEncoding.encodeRun
        Counting.Algorithm.KarpLuby.Examples.tautology (1 / 2) (1 / 4)
        (fun i => decide (i.val % 4 = 0 ∧ (i.val / 4) % 2 = 1))))
  unless serialized == some 8 do throw (IO.userError "serialized request pipeline returned an incorrect value")
  IO.println s!"{ns}: fixed-tape executable checks"
  IO.println s!"duplicate/contradiction/missing-variable trials: {Counting.Algorithm.KarpLuby.Examples.trialTable Counting.Algorithm.KarpLuby.Examples.overlapping}"
  IO.println s!"support average (expected 6): {Counting.Algorithm.KarpLuby.Examples.supportAverage Counting.Algorithm.KarpLuby.Examples.overlapping}"
  IO.println s!"two-group pipeline (expected 6): {overlap}"
  IO.println s!"rational request ε=1/2, δ=1/4 (expected 8): {exact}"
  IO.println s!"full serialized evaluator (expected some 8): {serialized}"
  IO.println s!"encoded output (expected (8,1)): {Counting.Algorithm.KarpLuby.Program.encodeOutput exact}"
  IO.println s!"decoded bit output (expected some 8): {Counting.Algorithm.KarpLuby.Encoding.decodeOutput (Counting.Algorithm.KarpLuby.Encoding.encodeOutput exact)}"
  IO.println s!"input roundtrip (expected some (3,4)): {Counting.Algorithm.KarpLuby.Examples.inputRoundtrip}"
  IO.println s!"empty DNF average (expected 0): {Counting.Algorithm.KarpLuby.Examples.supportAverage Counting.Algorithm.KarpLuby.Examples.noTerms}"
  IO.println s!"nullary empty term average (expected 1): {Counting.Algorithm.KarpLuby.Examples.supportAverage Counting.Algorithm.KarpLuby.Examples.nullaryTrue}"
