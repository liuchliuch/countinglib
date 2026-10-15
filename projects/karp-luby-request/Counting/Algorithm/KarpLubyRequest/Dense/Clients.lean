import Counting.Algorithm.KarpLubyRequest.Dense.FormulaCall

/-!
# Concrete clients of the actual formula normalizer

These executions specialize the proved finite program; no evaluator is supplied
as an assumption. They retain isolated variables, multiplicities, empty terms,
and the original total decoder's noncanonical natural words.
-/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Clients
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

/-- Two equal clauses stay duplicated; the contradictory clause disappears.
Variable 0 and variable 2 remain represented in each retained row. -/
def repeatedFormula : DNF.Formula 3 :=
  [[(0, true), (0, false)], [(1, true)], [(1, true)], []]

def repeatedRows : List CellCodec.Cells :=
  [[none, some true, none], [none, some true, none], [none, none, none]]

theorem repeated_value : (DenseNormalization.formula 3 repeatedFormula).value = repeatedRows := by decide

theorem repeated_actual :
    ∃ bit : Bool, ∃ time : ℕ,
      time ≤ Formula.rawCost 3 ((Encoding.formula 3).encode repeatedFormula).length ∧
      RunsExactly Formula.computer.step
        (cfg .copy (Formula.cleanMemory false)
          (Formula.bank [true, false, true] ((Encoding.formula 3).encode repeatedFormula) [] [] [] [] [] []))
        (cfg .good (Formula.cleanMemory bit)
          (Formula.outputBank [true, false, true] ((Encoding.formula 3).encode repeatedFormula)
            (encodeNat 3) (CellCodec.rows repeatedRows))) time := by
  have run := Formula.formula_raw false [true, false, true]
    ((Encoding.formula 3).encode repeatedFormula) repeatedFormula ((Encoding.formula 3).decode_encode repeatedFormula)
  have hvalue : (DenseNormalization.formula ([true, false, true] : List Bool).length repeatedFormula).value =
      repeatedRows := repeated_value
  rw [hvalue] at run
  simpa only [show ([true, false, true] : List Bool).length = 3 from rfl,
    show repeatedRows.length = 3 from rfl] using run

/-- The noncanonical word `[false]` decodes to 2 under the fixed source codec. -/
def rawLiteral : List Bool := Encoding.frame [false] ++ [true]
def rawTerm : List Bool := Encoding.frame [false] ++ Encoding.frames [rawLiteral, rawLiteral]
def rawFormula : List Bool := Encoding.frame [false] ++ Encoding.frames [rawTerm, rawTerm]
def rawValue : DNF.Formula 3 := [[(2, true), (2, true)], [(2, true), (2, true)]]

theorem raw_decode : (Encoding.formula 3).decode rawFormula = some rawValue := by decide

theorem raw_rows : (DenseNormalization.formula 3 rawValue).value =
    [[none, none, some true], [none, none, some true]] := by decide

theorem noncanonical_actual :
    ∃ bit : Bool, ∃ time : ℕ, time ≤ Formula.rawCost 3 rawFormula.length ∧
      RunsExactly Formula.computer.step
        (cfg .copy (Formula.cleanMemory false) (Formula.bank [false, true, false] rawFormula [] [] [] [] [] []))
        (cfg .good (Formula.cleanMemory bit)
          (Formula.outputBank [false, true, false] rawFormula (encodeNat 2)
            (CellCodec.rows [[none, none, some true], [none, none, some true]]))) time := by
  have run := Formula.formula_raw false [false, true, false] rawFormula rawValue raw_decode
  have hvalue : (DenseNormalization.formula ([false, true, false] : List Bool).length rawValue).value =
      [[none, none, some true], [none, none, some true]] := raw_rows
  rw [hvalue] at run
  simpa only [show ([false, true, false] : List Bool).length = 3 from rfl,
    show ([[none, none, some true], [none, none, some true]] : List CellCodec.Cells).length = 2 from rfl] using run

/-- Zero variables with one empty term is a successful empty dense row. Its
single false frame delimiter and count 1 differ from an empty formula. -/
theorem zero_variable_empty_term :
    ∃ bit : Bool, ∃ time : ℕ,
      time ≤ Formula.rawCost 0 ((Encoding.formula 0).encode [[]]).length ∧
      RunsExactly Formula.computer.step
        (cfg .copy (Formula.cleanMemory false) (Formula.bank [] ((Encoding.formula 0).encode [[]]) [] [] [] [] [] []))
        (cfg .good (Formula.cleanMemory bit)
          (Formula.outputBank [] ((Encoding.formula 0).encode [[]]) (encodeNat 1) [false])) time := by
  have run := Formula.formula_raw false [] ((Encoding.formula 0).encode [[]]) [[]]
    ((Encoding.formula 0).decode_encode [[]])
  simpa only [List.length_nil, DenseNormalization.formula, DenseNormalization.normalize,
    DenseNormalization.allocate, CellCodec.rows, CellCodec.encode, List.flatMap_nil,
    List.map_cons, List.map_nil, Encoding.frames, Encoding.frame, List.append_nil,
    List.length_cons] using run

/-- An empty formula over an explicitly nonempty variable set has no rows and
zero count. This also checks the final physical halt used by embedding callers. -/
theorem empty_formula_halts :
    ∃ bit : Bool, ∃ time : ℕ,
      time ≤ Formula.rawCost 3 ((Encoding.formula 3).encode []).length + 1 ∧
      RunsExactly Formula.computer.step
        (cfg .copy (Formula.cleanMemory false)
          (Formula.bank [false, true, false] ((Encoding.formula 3).encode []) [] [] [] [] [] []))
        (Formula.returned bit [false, true, false] ((Encoding.formula 3).encode []) [] []) time := by
  have run := Formula.formula_call false [false, true, false]
    ((Encoding.formula 3).encode []) [] ((Encoding.formula 3).decode_encode [])
  simpa only [List.length_cons, List.length_nil, DNF.normalizeFormula,
    List.filterMap_nil, DenseNormalization.formula, CellCodec.rows_nil,
    show encodeNat 0 = [] from rfl] using run

end Counting.Algorithm.KarpLubyRequest.Dense.Clients
