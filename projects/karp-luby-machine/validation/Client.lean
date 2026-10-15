import Counting.Algorithm.KarpLubyMachine

noncomputable section

open Counting.Algorithm.KarpLuby
open Counting.Algorithm.KarpLubyMachine

example : (DenseNormalization.formula 3 ([[]] : DNF.Formula 3)).value =
    [[none, none, none]] := rfl

example : (DenseNormalization.formula 2
    ([[(⟨0, by decide⟩, true), (⟨0, by decide⟩, false)]] : DNF.Formula 2)).value = [] := rfl

example : (DenseNormalization.formula 2
    ([[(⟨0, by decide⟩, true), (⟨0, by decide⟩, true)]] : DNF.Formula 2)).value =
    [[some true, none]] := rfl

example : (NumeratorMedian.median 4 ![5, 1, 5, 0]).value = 5 := by decide
example : (NumeratorMedian.median 4 ![1, 1, 0, 0]).value = 1 := by decide
example : (NumeratorMedian.median 0 Fin.elim0).value = 0 := rfl

example {n : ℕ} (cs : List (DNF.Clause n)) (s g : ℕ)
    (t : CoinTape (Program.randomBitBudget cs s g)) :
    Program.estimate cs s g t = ((NumeratorMedian.estimate cs s g t).value : ℚ) / s :=
  NumeratorMedian.estimate_refines cs s g t

example (r : ProgramEncoding.Request) :
    (RequestProgram.evalRequest r).value = ProgramEncoding.evalRequest r :=
  RequestProgram.evalRequest_value r

example {n : ℕ} (f : DNF.Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    Turing.TM2OutputsInTime FractionNormalization.computer
      (FractionNormalization.inputEncoding.encode
        (((NumeratorMedian.estimate (DNF.normalizeFormula f)
          (Program.requestedSamples (DNF.normalizeFormula f) epsilon)
          (Program.requestedGroups delta) tape).value : ℤ),
          Program.requestedSamples (DNF.normalizeFormula f) epsilon))
      (some (FractionNormalization.componentEncoding.encode
        (FractionNormalization.components (Program.run f epsilon delta tape))))
      (200 * (5 * f.length.size + 6 * epsilon.den.size + 2 * n + 38) ^ 3) :=
  FractionNormalization.requestOutputs f epsilon delta tape

-- These exact costs detect the missing per-observation vector read.
example : (NumeratorMedian.median 1 (fun _ => 7)).operations = 10 := by decide
example : (NumeratorMedian.median 4 (fun _ => 7)).operations = 73 := by decide
example : (NumeratorMedian.countBelow 4 (fun _ => 7) 6).operations = 8 := by decide
example : (NumeratorMedian.evalClause (n := 1) (fun _ => some true)
    (fun _ => true)).operations = 4 := rfl
example : (NumeratorMedian.evalClause (n := 1) (fun _ => none)
    (fun _ => true)).operations = 1 := rfl
