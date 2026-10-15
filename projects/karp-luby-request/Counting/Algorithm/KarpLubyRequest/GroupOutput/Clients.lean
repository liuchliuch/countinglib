import Counting.Algorithm.KarpLubyRequest.GroupOutput.Run

/-! Literal boundaries and actual source runs. The harness supplies each
caller-produced incoming word; its measured count covers append/finish source
calls, not production of the numerators or their delivery by the caller. -/
namespace Counting.Algorithm.KarpLubyRequest.GroupOutput.Clients
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby

example : Fintype.card Stack = 4 := by decide
example : Fintype.card Label = 6 := by decide
example : Fintype.card State = 3 := by decide
example : reversed [0, 0] = [false, false] := rfl
example : reversed [1, 0] = [false, false, true, true] := rfl
example : Median.input [] = [false] := rfl

/-- Bounded observation of the displayed TM2 transitions. -/
def observe : ℕ → computer.Cfg → Option (ℕ × computer.Cfg)
  | 0, c => if c.l.isNone then some (0, c) else none
  | fuel + 1, c =>
    if c.l.isNone then some (0, c)
    else (computer.step c).bind fun next => (observe fuel next).map fun p => (p.1 + 1, p.2)

def execute (c : computer.Cfg) : IO (ℕ × computer.Cfg) := do
  match observe 100000 c with
  | none => throw (IO.userError "group output source failed to halt")
  | some result => pure result

def checkSequence (name : String) (xs : List ℕ) : IO Unit := do
  let count := encodeNat xs.length
  let mut acc : List Bool := []
  let mut pref : List ℕ := []
  let mut measured : ℕ := 0
  for a in xs do
    let (steps, ending) ← execute (cfg .append () (bank (encodeNat a) acc [] count))
    pref := pref ++ [a]
    unless ending.stk 0 == [] && ending.stk 1 == reversed pref &&
        ending.stk 2 == [] && ending.stk 3 == count do
      throw (IO.userError (name ++ ": append bank/order/count mismatch"))
    unless ending.var == (none, ()) && steps == (encodeNat a).length + 1 do
      throw (IO.userError (name ++ ": append control or exact source count mismatch"))
    acc := ending.stk 1
    measured := measured + steps
  let (steps, ending) ← execute (cfg .reverse () (bank [] acc [] count))
  unless ending.stk 0 == Median.input xs && ending.stk 1 == [] &&
      ending.stk 2 == [] && ending.stk 3 == [] do
    throw (IO.userError (name ++ ": final Median input or work cleanup mismatch"))
  unless ending.var == (none, ()) && steps == (Median.input xs).length + 4 do
    throw (IO.userError (name ++ ": finish control or exact source count mismatch"))
  measured := measured + steps
  unless measured == appendTime xs + (Median.input xs).length + 4 do
    throw (IO.userError (name ++ ": combined source-call accounting mismatch"))
  unless measured ≤ 2 * (Median.input xs).length + 4 do
    throw (IO.userError (name ++ ": linear source-call bound exceeded"))
  IO.println (name ++ ": actual append/finish calls used " ++ toString measured ++ " transitions")

#eval checkSequence "no groups" []
#eval checkSequence "one zero group" [0]
#eval checkSequence "zero and repeated groups" [0, 0, 5, 0]
#eval checkSequence "ordered unequal values" [9, 1, 8, 2]
#eval checkSequence "binary width boundaries" [0, 1, 2, 3, 7, 8, 15, 16, 255, 256]
#eval checkSequence "ties retain occurrence count" [7, 2, 7, 0]

end Counting.Algorithm.KarpLubyRequest.GroupOutput.Clients
