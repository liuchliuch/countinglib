import Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody.Orbit

/-! Actual executions of the serialized sample body, including its exact time,
canonical accumulation, literal tape suffix, and all 21 physical stacks. -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody.Clients
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing

local instance : BEq computer.σ := inferInstanceAs (BEq Trial.State)

private def trialStackList : List Trial.Stack :=
  [.rows, .mass, .random, .rank, .remaining, .row, .rowMass, .history, .clock, .left,
   .right, .work, .arithmeticOutput, .scratch, .massRow, .assignment, .assignmentCopy, .output]

def stackList : List Stack := trialStackList.map Sum.inl ++ [.inr 0, .inr 1, .inr 2]

theorem stackList_complete (k : Stack) : k ∈ stackList := by
  cases k with
  | inl k => cases k <;> simp [stackList, trialStackList]
  | inr k => fin_cases k <;> simp [stackList]

/-- This observer only inspects the actual finite transition function. -/
def observe : ℕ → computer.Cfg → Option (ℕ × computer.Cfg)
  | 0, c => if c.l.isNone then some (0, c) else none
  | fuel + 1, c =>
    if c.l.isNone then some (0, c)
    else (computer.step c).bind fun next => (observe fuel next).map fun p => (p.1 + 1, p.2)

def check (name : String) (n : ℕ) (rows : List RowSemantics.Cells) (acc : ℕ) (bits : List Bool) : IO Unit := do
  let rowWord := Dense.CellCodec.rows rows
  let massWord := encodeNat (TotalMass.rowSum rows)
  let suffix := [true, false, true, true]
  unless bits.length == massWord.length && rows.all (fun row => row.length == n) do
    throw (IO.userError (name ++ ": test shape or fair-prefix length mismatch"))
  let input := word rowWord massWord (encodeNat acc) (bits ++ suffix)
  let b := TrialSpec.trialValue rows (BinaryArithmetic.value bits.reverse)
  let output := word rowWord massWord (encodeNat (acc + b)) suffix
  let expected := halted output
  let expectedTime := sourceTime n rows (acc, bits ++ suffix)
  match observe (expectedTime + 1) (initList computer input) with
  | none => throw (IO.userError (name ++ ": sample body did not halt"))
  | some (time, finish) =>
    unless time == expectedTime do
      throw (IO.userError (name ++ ": actual and specified transition totals differ"))
    unless finish.l.isNone && finish.var == Trial.initial &&
        stackList.all (fun k => finish.stk k == expected.stk k) do
      throw (IO.userError (name ++ ": accumulation, suffix, output framing, or full cleanup mismatch"))
    let measured := Primitive.run program time (some (initList computer input))
    unless measured.1 ≤ 9 * time do
      throw (IO.userError (name ++ ": primitive source budget mismatch"))
    match measured.2 with
    | none => throw (IO.userError (name ++ ": primitive observer failed"))
    | some ending =>
      unless ending.l.isNone && ending.var == Trial.initial &&
          stackList.all (fun k => ending.stk k == finish.stk k) do
        throw (IO.userError (name ++ ": primitive and transition observers disagree"))
    IO.println (name ++ ": " ++ toString time ++ " actual transitions; " ++
      toString measured.1 ++ " primitive instructions; accumulator " ++ toString (acc + b))

#eval check "empty zero-width sample preserves accumulator" 0 [] 31 []
#eval check "nullary accepted sample" 0 [[]] 0 [false]
#eval check "padding sample preserves accumulator" 0 [[]] 7 [true]
#eval check "free sample carries accumulator" 1 [[none]] 255 [false, true]
#eval check "duplicate later sample contributes zero" 1 [[none], [none]] 15 [false, true, false]
#eval check "disjoint second sample contributes scale" 1 [[some false], [some true]] 3 [false, true]

end Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody.Clients
