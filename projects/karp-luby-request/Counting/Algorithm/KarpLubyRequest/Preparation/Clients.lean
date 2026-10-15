import Counting.Algorithm.KarpLubyRequest.Preparation.RawBounds
import Counting.Algorithm.KarpLubyRequest.Preparation.Classification

/-!
# Boundary clients of the actual all-raw preparation theorem

These are kernel-checked specializations of the actual finite source execution
and physical polynomial bound. They are not VM smoke tests. Expected words are
checked separately against the original request grammar; no semantic executor
is supplied to the source machine.
-/
namespace Counting.Algorithm.KarpLubyRequest.Preparation.Clients
noncomputable section
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- Explicit reduced data keeps the concrete codec checks independent of
typeclass division's proof-bearing normalization wrapper. -/
def half : ℚ := ⟨1, 2, by decide, by decide⟩
def smallAccuracy : ℚ := ⟨1, 1024, by decide, by decide⟩

abbrev Executes (raw word : List Bool) : Prop :=
  ∃ time, time ≤ rawBound raw.length ∧
    RunsExactly computer.step (initList computer raw) (haltList computer word) time

private theorem actual_of_result (raw word : List Bool) (h : rawResult raw = word) :
    Executes raw word := by
  have run := raw_run_bounded raw
  rw [h] at run
  exact run

private theorem canonical_result (r : ProgramEncoding.Request) :
    rawResult (ProgramEncoding.request.encode r) = requestResult r := by
  simp only [rawResult, ProgramEncoding.request.decode_encode, Option.elim_some]

/-- An absent outer delimiter is rejected, and the entire dirty bank is cleared. -/
theorem empty_raw : Executes [] [false] :=
  actual_of_result [] [false] rfl

/-- A large binary list declaration with no body fails the original decoder.
The charged bound depends on the physical header word, not its declared value. -/
def enormousDeclaration : List Bool :=
  Contract.join ⟨Encoding.frame [true, false, true] ++
    Encoding.frame (encodeNat (2 ^ 64)), Encoding.encodeOutput 1,
    Encoding.encodeOutput half, [false, true]⟩

theorem enormous_declaration_malformed :
    (ProgramEncoding.request.decode enormousDeclaration).isSome = false := by decide

theorem enormous_declaration_actual : Executes enormousDeclaration [false] :=
  actual_of_result enormousDeclaration [false] (by decide)

/-- Two opposite occurrences eliminate the term; both unused variables remain
in the input. The tape deliberately has the wrong length and is still cleared
by the earlier zero-mass branch, without running sample/group arithmetic. -/
def contradictoryRequest : ProgramEncoding.Request :=
  ⟨⟨3, [[(0, true), (0, false)]]⟩, smallAccuracy, half, [true, false, true]⟩

theorem contradictory_result : requestResult contradictoryRequest = [false] := by decide

theorem contradictory_actual :
    Executes (ProgramEncoding.request.encode contradictoryRequest) [false] :=
  actual_of_result _ _ ((canonical_result contradictoryRequest).trans contradictory_result)

/-- Zero variables and an empty DNF also take the zero-mass shortcut. -/
def emptyFormulaRequest : ProgramEncoding.Request := ⟨⟨0, []⟩, 1, half, [true]⟩

theorem empty_formula_actual :
    Executes (ProgramEncoding.request.encode emptyFormulaRequest) [false] :=
  actual_of_result _ _ ((canonical_result emptyFormulaRequest).trans (by decide))

/-- The empty term has positive mass even with no variables. A missing random
tape therefore fails the exact physical budget gate, rather than normalization. -/
def wrongTapeRequest : ProgramEncoding.Request := ⟨⟨0, [[]]⟩, 1, half, []⟩

theorem wrong_tape_positive_mass :
    Program.totalMass (DNF.normalizeFormula wrongTapeRequest.problem.formula) = 1 := by decide

theorem wrong_tape_actual :
    Executes (ProgramEncoding.request.encode wrongTapeRequest) [false] :=
  actual_of_result _ _ ((canonical_result wrongTapeRequest).trans (by decide))

/-- An invalid accuracy parameter is rejected before any dense/count stage. -/
def invalidParameterRequest : ProgramEncoding.Request := ⟨⟨1, [[]]⟩, 0, half, [false]⟩

theorem invalid_parameter_actual :
    Executes (ProgramEncoding.request.encode invalidParameterRequest) [false] :=
  actual_of_result _ _ ((canonical_result invalidParameterRequest).trans (by decide))

def noncanonicalLiteral : List Bool := Encoding.frame [false] ++ [true]
def noncanonicalTerm : List Bool :=
  Encoding.frame [false] ++ Encoding.frames [noncanonicalLiteral, noncanonicalLiteral]
def noncanonicalFormula : List Bool :=
  Encoding.frame [false] ++ Encoding.frames [noncanonicalTerm, noncanonicalTerm]
def noncanonicalRequest : List Bool :=
  Contract.join ⟨Encoding.frame [false, true, false] ++ noncanonicalFormula,
    Encoding.encodeOutput 1, Encoding.encodeOutput half, []⟩

/-- Both binary list headers and the index use all-false noncanonical words.
The arbitrary-bit unary variable header still declares three variables. -/
theorem noncanonical_decoded :
    (ProgramEncoding.request.decode noncanonicalRequest).map
      (fun r => (r.problem.variableCount, Program.totalMass (DNF.normalizeFormula r.problem.formula))) =
      some (3, 8) := by decide

theorem noncanonical_actual : Executes noncanonicalRequest [false] :=
  actual_of_result _ _ (by decide)

/-- A positive, exactly budgeted request preserves its tape literally and
serializes the canonical mass, samples and groups after the zero-variable row. -/
def positiveTape : List Bool := List.replicate 3456 false
def positiveRequest : ProgramEncoding.Request := ⟨⟨0, [[]]⟩, 1, half, positiveTape⟩

theorem positive_result : requestResult positiveRequest =
    payload (Dense.CellCodec.rows [[]]) (encodeNat 1) (encodeNat 576) (encodeNat 6) positiveTape := by
  decide

theorem positive_actual : Executes (ProgramEncoding.request.encode positiveRequest)
    (payload (Dense.CellCodec.rows [[]]) (encodeNat 1) (encodeNat 576) (encodeNat 6) positiveTape) :=
  actual_of_result _ _ ((canonical_result positiveRequest).trans positive_result)

end
end Counting.Algorithm.KarpLubyRequest.Preparation.Clients
