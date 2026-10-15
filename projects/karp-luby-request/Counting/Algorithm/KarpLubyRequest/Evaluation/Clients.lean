import Counting.Algorithm.KarpLubyRequest.Evaluation.Run

/-!
# Executions of the complete prepared-payload evaluator

Every client starts the actual finite program at its entry label. Expected
answers are computed by the original rational estimator, then compared as the
original literal output encoding. Both transition and primitive interpreters
must halt with every physical stack and finite register in the final bank.
The positive payloads contain exactly their consumed random-tape budget.
-/
namespace Counting.Algorithm.KarpLubyRequest.Evaluation.Clients
open Turing Computability Holant.Complexity StackProtocol BinaryCompose GraphPreprocessing
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine
open Sampling
open scoped BigOperators
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

local instance : BEq GroupBody.machine.State :=
  inferInstanceAs (BEq (Option Bool × Trial.State))
local instance : BEq OuterState :=
  inferInstanceAs (BEq (Option Bool × (Option Bool × Trial.State)))
local instance : BEq computer.σ := inferInstanceAs (BEq State)

private def trialStackList : List Trial.Stack :=
  [.rows, .mass, .random, .rank, .remaining, .row, .rowMass, .history, .clock, .left,
   .right, .work, .arithmeticOutput, .scratch, .massRow, .assignment, .assignmentCopy, .output]

private def sampleStackList : List SampleBody.Stack :=
  trialStackList.map Sum.inl ++ (List.finRange 3).map Sum.inr

private def innerStackList : List GroupBody.InnerStack :=
  (List.finRange 3).map Sum.inl ++ sampleStackList.map Sum.inr

private def groupStackList : List GroupBody.Stack :=
  innerStackList.map Sum.inl ++ (List.finRange 6).map Sum.inr

private def outerStackList : List OuterStack :=
  (List.finRange 3).map Sum.inl ++ groupStackList.map Sum.inr

private def medianStackList : List Median.Program.Stack :=
  [.input, .saved, .inner, .candidate, .chosen, .left, .right, .work,
   .answer, .temp, .below, .above]

private def outputStackList : List Output.Program.Stack :=
  [.inl (.inl .input), .inl (.inl .divisor), .inl (.inl .remainder),
   .inl (.inl .divisorRev), .inl (.inl .oldRev), .inl (.inl .trialRev),
   .inl (.inl .quotient), .inl (.inr .saved), .inl (.inr .temp),
   Output.Program.ex .num, Output.Program.ex .den, Output.Program.ex .temp,
   Output.Program.ex .gcd, Output.Program.ex .stream]

/-- A computable exhaustive list of all 65 physical stacks. -/
def stackList : List Stack :=
  outerStackList.map Sum.inl ++
    ((List.finRange 6).map Sum.inl ++
      (medianStackList.map Sum.inl ++ outputStackList.map Sum.inr).map Sum.inr).map Sum.inr

private theorem sumList_complete {α β : Type} (left : List α) (right : List β)
    (hl : ∀ a, a ∈ left) (hr : ∀ b, b ∈ right) (k : α ⊕ β) :
    k ∈ left.map Sum.inl ++ right.map Sum.inr := by
  cases k with
  | inl a => exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨a, hl a, rfl⟩))
  | inr b => exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨b, hr b, rfl⟩))

private theorem trialStackList_complete (k : Trial.Stack) : k ∈ trialStackList := by
  cases k <;> decide

private theorem sampleStackList_complete (k : SampleBody.Stack) : k ∈ sampleStackList :=
  sumList_complete _ _ trialStackList_complete List.mem_finRange k

private theorem innerStackList_complete (k : GroupBody.InnerStack) : k ∈ innerStackList :=
  sumList_complete _ _ List.mem_finRange sampleStackList_complete k

private theorem groupStackList_complete (k : GroupBody.Stack) : k ∈ groupStackList :=
  sumList_complete _ _ innerStackList_complete List.mem_finRange k

private theorem outerStackList_complete (k : OuterStack) : k ∈ outerStackList :=
  sumList_complete _ _ List.mem_finRange groupStackList_complete k

private theorem medianStackList_complete (k : Median.Program.Stack) : k ∈ medianStackList := by
  cases k <;> decide

private theorem outputStackList_complete (k : Output.Program.Stack) : k ∈ outputStackList := by
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [outputStackList]
    | inr k => cases k <;> simp [outputStackList]
  | inr k => cases k <;> simp [outputStackList]

theorem stackList_complete (k : Stack) : k ∈ stackList :=
  sumList_complete _ _ outerStackList_complete
    (sumList_complete _ _ List.mem_finRange
      (sumList_complete _ _ medianStackList_complete outputStackList_complete)) k

example : stackList.length = 65 := by decide

/-- Direct access to the same transition function avoids materializing the
bundled enumeration of the product of all finite register types. -/
private def stackDecidable : DecidableEq Stack :=
  inferInstanceAs (DecidableEq
    (OuterStack ⊕ (Fin 6 ⊕ (Median.Program.Stack ⊕ Output.Program.Stack))))

def transition : computer.Cfg → Option computer.Cfg :=
  @TM2.step Stack (fun _ => Bool) Label State stackDecidable program

theorem transition_eq : transition = computer.step := rfl

def startConfiguration (input : List Bool) : computer.Cfg :=
  ⟨some .dispatch, initial, @wordTape Stack stackDecidable random input⟩

theorem startConfiguration_eq (input : List Bool) :
    startConfiguration input = initList computer input := (Machine.init_eq machine input).symm

/-- The same syntactic budget only needs the finite label enumeration. -/
def instructionBudget : ℕ := ∑ label : Label, TM2Cost.budget (program label)

theorem instructionBudget_eq : instructionBudget = machine.primitiveBudget := rfl

/-- The observer executes only the displayed TM2 transition function. -/
def observe : ℕ → computer.Cfg → Option (ℕ × computer.Cfg)
  | 0, c => if c.l.isNone then some (0, c) else none
  | fuel + 1, c => if c.l.isNone then some (0, c) else
      (transition c).bind fun next =>
        (observe fuel next).map fun p => (p.1 + 1, p.2)

def checkWord (name : String) (input : List Bool) (expected : ℚ)
    (exactTime : Option ℕ := none) : IO Unit := do
  let start := startConfiguration input
  let target := finalConfiguration (Encoding.encodeOutput expected)
  match observe 1000000 start with
  | none => throw (IO.userError (name ++ ": actual evaluator did not halt"))
  | some (time, ending) =>
    unless ending.l.isNone && ending.var == target.var &&
        stackList.all (fun k => ending.stk k == target.stk k) do
      throw (IO.userError (name ++ ": literal output, physical cleanup, or finite state differs"))
    if let some specified := exactTime then
      unless time == specified do
        throw (IO.userError (name ++ ": exact transition count differs"))
    let measured := @Primitive.run Stack Label State stackDecidable program time (some start)
    unless measured.1 ≤ instructionBudget * time do
      throw (IO.userError (name ++ ": primitive instruction bound exceeded"))
    match measured.2 with
    | none => throw (IO.userError (name ++ ": primitive observer failed"))
    | some finish =>
      unless finish.l.isNone && finish.var == target.var &&
          stackList.all (fun k => finish.stk k == target.stk k) do
        throw (IO.userError (name ++ ": primitive and transition observers disagree"))
    IO.println (name ++ ": " ++ toString time ++ " actual transitions, " ++
      toString measured.1 ++ " primitive instructions, value " ++ toString expected)

/-- Prepared positive payloads are checked directly against the original
rational estimator; the explicit value also checks each chosen tape scenario. -/
def checkPositive (name : String) (n : ℕ) (rowData : List RowSemantics.Cells)
    (sampleCount groupCount : ℕ) (tape : List Bool) (value : ℚ) : IO Unit := do
  unless rowData.all (fun row => row.length == n) do
    throw (IO.userError (name ++ ": row widths differ"))
  let cs := rowData.map (DenseNormalization.denote n)
  unless tape.length == Counting.Algorithm.KarpLuby.Program.randomBitBudget cs sampleCount groupCount do
    throw (IO.userError (name ++ ": tape does not have the exact original budget"))
  let expected := Counting.Algorithm.KarpLuby.Program.estimate cs sampleCount groupCount
    (fun i => tape.getD i.val false)
  unless expected == value do
    throw (IO.userError (name ++ ": original estimator disagrees with the scenario value"))
  checkWord name
    (payload (Dense.CellCodec.rows rowData) (encodeNat (TotalMass.rowSum rowData))
      (encodeNat sampleCount) (encodeNat groupCount) tape) expected

example : ∃ time, time ≤ timeBound 0 [[]] 1 1 [false] ∧
    RunsExactly computer.step
      (initList computer (payload (Dense.CellCodec.rows [[]]) (encodeNat 1)
        (encodeNat 1) (encodeNat 1) [false]))
      (haltList computer (Encoding.encodeOutput 2)) time := by
  have hrows : ∀ row ∈ ([[]] : List RowSemantics.Cells), row.length = 0 := by
    intro row h
    simp only [List.mem_singleton] at h
    subst row
    rfl
  have hg : (groupResult 0 [[]] 1 1 [false]).1 = [2] := by decide
  have hm : Median.value [2] = 2 := by decide
  have hv : resultValue 0 [[]] 1 1 [false] = 2 := by
    rw [resultValue, hg, hm]
    norm_num
  have hmass : TotalMass.rowSum [[]] = 1 := by decide
  simpa only [hv, hmass] using prepared_run 0 [[]] hrows 1 1 [false] (by decide)

example : ∃ time, time ≤ timeBound 0 [[]] 3 1 [false,true,true] ∧
    RunsExactly computer.step
      (initList computer (payload (Dense.CellCodec.rows [[]]) (encodeNat 1)
        (encodeNat 3) (encodeNat 1) [false,true,true]))
      (haltList computer (Encoding.encodeOutput (2 / 3))) time := by
  have hrows : ∀ row ∈ ([[]] : List RowSemantics.Cells), row.length = 0 := by
    intro row h
    simp only [List.mem_singleton] at h
    subst row
    rfl
  have hg : (groupResult 0 [[]] 3 1 [false,true,true]).1 = [2] := by decide
  have hm : Median.value [2] = 2 := by decide
  have hv : resultValue 0 [[]] 3 1 [false,true,true] = 2 / 3 := by
    rw [resultValue, hg, hm]
    norm_num
  have hmass : TotalMass.rowSum [[]] = 1 := by decide
  simpa only [hv, hmass] using prepared_run 0 [[]] hrows 3 1 [false,true,true] (by decide)

example : RunsExactly computer.step (initList computer [false])
    (haltList computer (Encoding.encodeOutput 0)) 2 := zero_run

#eval checkWord "false tag literal zero" [false] 0 (some 2)
#eval checkPositive "empty formula and zero-width samples" 0 [] 2 2 [] 0
#eval checkPositive "zero samples" 0 [[]] 0 2 [] 0
#eval checkPositive "zero groups" 0 [[]] 2 0 [] 0
#eval checkPositive "nullary clause accepts rank zero" 0 [[]] 1 1 [false] 2
#eval checkPositive "nullary clause rejects padding rank" 0 [[]] 1 1 [true] 0
#eval checkPositive "two groups retain upper median" 0 [[]] 1 2 [false,true] 2
#eval checkPositive "proper fraction from three actual samples" 0 [[]] 3 1 [false,true,true] (2 / 3)
#eval checkPositive "duplicate clauses preserve first owner" 1 [[none],[none]] 1 2
  [false,false,false,false,true,false] 8

end Counting.Algorithm.KarpLubyRequest.Evaluation.Clients
