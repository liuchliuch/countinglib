import Counting.Algorithm.KarpLubyRequest.Sampling.TrialBank
import Counting.Algorithm.KarpLubyRequest.Sampling.TrialSpec
import Counting.Algorithm.KarpLubyRequest.Sampling.TrialBudget

/-! Actual execution checks for padding, ownership, fair-bit order, cleanup,
and the materialized dyadic output. The inputs are prepared physical banks. -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Trial.Clients
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing

def stackList : List Stack := [.rows, .mass, .random, .rank, .remaining, .row, .rowMass, .history, .clock, .left, .right, .work, .arithmeticOutput, .scratch, .massRow, .assignment, .assignmentCopy, .output]
theorem stackList_complete (k : Stack) : k ∈ stackList := by cases k <;> simp [stackList]

def observe : ℕ → computer.Cfg → Option (ℕ × computer.Cfg)
  | 0, c => if c.l.isNone then some (0, c) else none
  | fuel + 1, c =>
    if c.l.isNone then some (0, c)
    else (computer.step c).bind fun next => (observe fuel next).map fun p => (p.1 + 1, p.2)

def check (name : String) (rows : List RowSemantics.Cells) (bits : List Bool) : IO Unit := do
  let rowWord := Dense.CellCodec.rows rows
  let massWord := encodeNat (TotalMass.rowSum rows)
  let suffix := [true, false, true, true]
  unless bits.length == massWord.length do
    throw (IO.userError (name ++ ": test fair-prefix length mismatch"))
  let start := configuration .clockMove initial (inputData rowWord massWord (bits ++ suffix))
  match observe 100000 start with
  | none => throw (IO.userError (name ++ ": trial did not halt"))
  | some (time, finish) =>
    let r := BinaryArithmetic.value bits.reverse
    let expected := finalConfiguration rowWord massWord suffix (encodeNat (TrialSpec.trialValue rows r))
    unless finish.l.isNone && finish.var == initial &&
        stackList.all (fun k => finish.stk k == expected.stk k) do
      throw (IO.userError (name ++ ": branch, suffix, output, or complete cleanup mismatch"))
    let measured := Primitive.run program time (some start)
    unless measured.1 ≤ 9 * time do
      throw (IO.userError (name ++ ": primitive source budget mismatch"))
    match measured.2 with
    | none => throw (IO.userError (name ++ ": primitive observer failed"))
    | some ending =>
      unless ending.l.isNone && ending.var == initial &&
          stackList.all (fun k => ending.stk k == finish.stk k) do
        throw (IO.userError (name ++ ": primitive/transition observers disagree"))
    IO.println (name ++ ": " ++ toString time ++ " actual transitions; " ++
      toString measured.1 ++ " primitive instructions")

#eval check "empty zero-width union" [] []
#eval check "zero-variable occurrence accepted" [[]] [false]
#eval check "zero-variable padding rejected" [[]] [true]
#eval check "one free variable rank zero" [[none]] [false, false]
#eval check "one free variable rank one" [[none]] [false, true]
#eval check "duplicate first occurrence accepted" [[none], [none]] [false, false, false]
#eval check "duplicate later occurrence rejected" [[none], [none]] [false, true, false]
#eval check "disjoint second occurrence accepted" [[some false], [some true]] [false, true]
#eval check "explicit 128 free variables" [List.replicate 128 none] (List.replicate 129 false)

end Counting.Algorithm.KarpLubyRequest.Sampling.Trial.Clients

