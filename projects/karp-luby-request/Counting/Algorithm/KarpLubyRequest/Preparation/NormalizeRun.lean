import Counting.Algorithm.KarpLubyRequest.Preparation.DenseInput
import Counting.Algorithm.KarpLubyRequest.Preparation.MassInput

/-! Complete accepted-source prefix through dense normalization and mass.
The original parser fields are physically retained, and the result is obtained
by the two actual source calls after their charged caller copies. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine
set_option backward.isDefEq.respectTransparency false

def workingMemory (bit : Bool) : Memory where
  parameter := (true, BinaryArithmetic.Comparison.initial)
  counts := initialMemory.counts
  formula := (bit, IntegerArithmetic.CarryProtocol.clean (false, false))
  mass := initialMemory.mass
  budget := initialMemory.budget

def normalizedRows (source : RequestParser.Stack → List Bool)
    (f : DNF.Formula (variableWord source).length) : List Sampling.RowSemantics.Cells :=
  (DenseNormalization.formula (variableWord source).length f).value

def denseResult (source : RequestParser.Stack → List Bool)
    (f : DNF.Formula (variableWord source).length) : Data :=
  {validatedData source with formula := (Dense.Formula.outputBank
    (variableWord source) (formulaWord source) (encodeNat (DNF.normalizeFormula f).length)
    (Dense.CellCodec.rows (normalizedRows source f)))}

def normalizedData (source : RequestParser.Stack → List Bool)
    (f : DNF.Formula (variableWord source).length) : Data :=
  massData (denseResult source f) (normalizedRows source f)

def normalizationCost (source : RequestParser.Stack → List Bool)
    (f : DNF.Formula (variableWord source).length) : ℕ :=
  (Sampling.TotalMass.runTime (normalizedRows source f) 0 +
    (2 * (Dense.CellCodec.rows (normalizedRows source f)).length + 2)) +
  (Dense.Formula.rawCost (variableWord source).length (formulaWord source).length + 1) +
  (2 * ((variableWord source).length + (formulaWord source).length) + 4) + 1

theorem normalize_mass (source : RequestParser.Stack → List Bool)
    (f : DNF.Formula (variableWord source).length)
    (hd : (Encoding.formula (variableWord source).length).decode (formulaWord source) = some f) :
    ∃ bit time, time ≤ normalizationCost source f ∧
      RunsExactly computer.step
        (configuration .validated (none, workingMemory false) (validatedData source))
        (configuration .massCheck (none, workingMemory bit) (normalizedData source f)) time := by
  have branch := validated_true (workingMemory false) (validatedData source).tapes rfl
  have copy := dense_input_copy source (workingMemory false)
  obtain ⟨bit, time, bound, dense⟩ := formula_call (validatedData source) (workingMemory false)
    false (variableWord source) (formulaWord source) f hd
  have mass := mass_after_dense (denseResult source f) (workingMemory bit)
    (normalizedRows source f) rfl rfl rfl
  have run := ((branch.trans copy).trans dense).trans mass
  refine ⟨bit, _, ?_, run⟩
  dsimp only [normalizationCost]
  omega

def normalizationPolynomialBound (n : ℕ) : ℕ :=
  20 * (n * (4 * n + 1) + 1) ^ 2 + 2 * (n * (4 * n + 1)) +
    23 * n ^ 2 + 80 * n + 19

/-- Every loop in the preceding real prefix is polynomial in its two physical
input lengths. The binary magnitude of a declared count is not a loop budget. -/
theorem normalization_cost_le (source : RequestParser.Stack → List Bool)
    (f : DNF.Formula (variableWord source).length)
    (hd : (Encoding.formula (variableWord source).length).decode (formulaWord source) = some f)
    (n : ℕ) (hn : (variableWord source).length ≤ n) (hr : (formulaWord source).length ≤ n) :
    normalizationCost source f ≤ normalizationPolynomialBound n := by
  have hraw := Dense.Formula.rawCost_le_input (variableWord source).length (formulaWord source).length n hn hr
  have hrows := Dense.Formula.rows_length_le_raw (formulaWord source) f hd
  have hprod := Nat.mul_le_mul hr (show 4 * (variableWord source).length + 1 ≤ 4 * n + 1 by omega)
  have hlen : (Dense.CellCodec.rows (normalizedRows source f)).length ≤ n * (4 * n + 1) :=
    hrows.trans hprod
  have htime := Sampling.TotalMass.input_time_bound (normalizedRows source f)
  have hsquare := Nat.pow_le_pow_left (show (Dense.CellCodec.rows (normalizedRows source f)).length + 1 ≤
    n * (4 * n + 1) + 1 by omega) 2
  dsimp only [normalizationCost, normalizationPolynomialBound]
  omega

end
end Counting.Algorithm.KarpLubyRequest.Preparation
