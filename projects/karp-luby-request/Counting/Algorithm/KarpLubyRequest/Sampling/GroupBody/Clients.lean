import Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Bounds

/-! Actual finite-program executions: zero samples, empty variables, a rejected
dyadic rank, repeated samples, and ordered outer groups with a retained suffix. -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Clients
open Turing Computability Holant.Complexity StackProtocol BinaryCompose GraphPreprocessing
open Counting.Algorithm.KarpLuby
open Counting.Algorithm.KarpLubyMachine
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

local instance : BEq machine.State := inferInstanceAs (BEq (Option Bool × Trial.State))
local instance : BEq (Iteration.machine machine).State :=
  inferInstanceAs (BEq (Option Bool × (Option Bool × Trial.State)))
local instance : DecidableEq (Iteration.Stack machine) :=
  inferInstanceAs (DecidableEq (Fin 3 ⊕ machine.K))

private def trialStackList : List Trial.Stack :=
  [.rows, .mass, .random, .rank, .remaining, .row, .rowMass, .history, .clock, .left,
   .right, .work, .arithmeticOutput, .scratch, .massRow, .assignment, .assignmentCopy, .output]

private def sampleStackList : List SampleBody.Stack :=
  trialStackList.map Sum.inl ++ (List.finRange 3).map Sum.inr

private def innerStackList : List InnerStack :=
  (List.finRange 3).map Sum.inl ++ sampleStackList.map Sum.inr

/-- Computable enumeration of all physical stacks, including both loop banks. -/
def stackList : List Stack :=
  innerStackList.map Sum.inl ++ (List.finRange 6).map Sum.inr

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

private theorem innerStackList_complete (k : InnerStack) : k ∈ innerStackList :=
  sumList_complete _ _ List.mem_finRange sampleStackList_complete k

theorem stackList_complete (k : Stack) : k ∈ stackList :=
  sumList_complete _ _ innerStackList_complete List.mem_finRange k

def outerStackList : List (Iteration.Stack machine) :=
  (List.finRange 3).map Sum.inl ++ stackList.map Sum.inr

theorem outerStackList_complete (k : Iteration.Stack machine) : k ∈ outerStackList :=
  sumList_complete _ _ List.mem_finRange stackList_complete k

def observe (body : Machine) : ℕ → body.Config → Option (ℕ × body.Config)
  | 0, c => if c.l.isNone then some (0,c) else none
  | fuel+1, c => if c.l.isNone then some (0,c) else
      (body.computer.step c).bind fun next =>
        (observe body fuel next).map fun p => (p.1+1,p.2)

def check (name : String) (n : ℕ) (rows : List RowSemantics.Cells) (samples : ℕ)
    (history tape : List Bool) (numerator : ℕ) (suffix : List Bool) : IO Unit := do
  let rowWord := Dense.CellCodec.rows rows
  let massWord := encodeNat (TotalMass.rowSum rows)
  let input := word rowWord massWord (encodeNat samples) history tape
  let output := word rowWord massWord (encodeNat samples)
    ((Encoding.frame (encodeNat numerator)).reverse ++ history) suffix
  let start := initList computer input
  match observe machine 1000000 start with
  | none => throw (IO.userError (name ++ ": actual group machine did not halt"))
  | some (time, ending) =>
    unless ending.stk random == output do
      throw (IO.userError (name ++ ": incorrect complete serialized output"))
    unless stackList.all
        (fun k => if k = random then true else (ending.stk k).isEmpty) do
      throw (IO.userError (name ++ ": uncleared physical work stack"))
    unless ending.var == initial do
      throw (IO.userError (name ++ ": finite register not reset"))
    unless time == sourceTime n rows samples (history,tape) do
      throw (IO.userError (name ++ ": exact transition account mismatch"))
    let measured := Primitive.run program time (some start)
    unless measured.1 ≤ machine.primitiveBudget * time do
      throw (IO.userError (name ++ ": primitive instruction bound exceeded"))
    match measured.2 with
    | none => throw (IO.userError (name ++ ": primitive observer failed"))
    | some finish =>
      unless finish.l.isNone && stackList.all (fun k => finish.stk k == ending.stk k) do
        throw (IO.userError (name ++ ": primitive and transition observers disagree"))
    IO.println (name ++ ": " ++ toString time ++ " actual transitions, " ++
      toString measured.1 ++ " primitive instructions")

def checkGroups : IO Unit := do
  let rows : List RowSemantics.Cells := [[]]
  let tape := [false,true,true,false]
  let rowWord := Dense.CellCodec.rows rows
  let massWord := encodeNat (TotalMass.rowSum rows)
  let input := word rowWord massWord (encodeNat 1) [] tape
  let output := word rowWord massWord (encodeNat 1) (GroupOutput.reversed [2,0]) [true,false]
  let start := cfg (Iteration.own machine 0) machine.initial
    (Iteration.ready machine (encodeNat 2) input)
  match observe (Iteration.machine machine) 1000000 start with
  | none => throw (IO.userError "outer groups: actual machine did not halt")
  | some (time, ending) => do
    unless ending.stk (Iteration.bodyStack machine random) == output do
      throw (IO.userError "outer groups: numerator order or suffix mismatch")
    unless outerStackList.all
        (fun k => if k = Iteration.bodyStack machine random then true else (ending.stk k).isEmpty) do
      throw (IO.userError "outer groups: uncleared work or countdown")
    unless ending.var == (Iteration.machine machine).initial do
      throw (IO.userError "outer groups: finite register not reset")
    let expected := Iteration.ticks (stateEncoding rowWord massWord (encodeNat 1))
      (step (rows.map (DenseNormalization.denote 0)) 1 massWord.length)
      (sourceTime 0 rows 1) 2 ([],tape)
    unless time == expected do
      throw (IO.userError "outer groups: exact nested transition mismatch")
    let measured := Primitive.run (Iteration.program machine) time (some start)
    unless measured.1 ≤ (8 + machine.primitiveBudget) * time do
      throw (IO.userError "outer groups: primitive instruction bound exceeded")
    match measured.2 with
    | none => throw (IO.userError "outer groups: primitive observer failed")
    | some finish =>
      unless finish.l.isNone && outerStackList.all (fun k => finish.stk k == ending.stk k) do
        throw (IO.userError "outer groups: primitive and transition observers disagree")
    IO.println ("ordered groups [2,0] with suffix: " ++ toString time ++
      " actual transitions, " ++ toString measured.1 ++ " primitive instructions")

#eval check "zero samples keeps raw history and tape" 0 [[]] 0 [true,false] [true,false] 0 [true,false]
#eval check "one empty clause accepts rank zero" 0 [[]] 1 [] [false,true] 2 [true]
#eval check "one empty clause rejects rank one" 0 [[]] 1 [] [true,false] 0 [false]
#eval check "two real samples accumulate" 1 [[none]] 2 [] [false,false,false,false,true] 8 [true]
#eval checkGroups

end Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Clients
