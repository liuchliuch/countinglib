import Counting.Algorithm.KarpLubyRequest.Median.Machine

set_option maxRecDepth 8192

/-! Boundary cases and executions of the displayed finite transition program. -/
namespace Counting.Algorithm.KarpLubyRequest.Median.Clients
open Turing Computability Holant.Complexity.StackProtocol
open Program

example : value [] = 0 := rfl
example : value [0] = 0 := by decide
example : value [9, 0] = 9 := by decide
example : value [7, 2, 7, 0] = 7 := by decide
example : value [0, 0, 5, 0] = 0 := by decide
example : value [14, 1, 9, 9, 3] = 9 := by decide
example : value [10, 8, 6, 4, 2, 0] = 6 := by decide
example : value [65536, 0, 31, 32] = 32 := by decide

example : Fintype.card Stack = 12 := by decide
example : Fintype.card Label = 35 := by decide
example : Fintype.card State = 216 := by decide

/-- A test observer of actual TM2 transitions, with explicit finite fuel.
It does not implement or stand in for the median algorithm. -/
def observe : ℕ → computer.Cfg → Option (ℕ × computer.Cfg)
  | 0, c => if c.l.isNone then some (0, c) else none
  | fuel + 1, c =>
    if c.l.isNone then some (0, c)
    else (computer.step c).bind fun next => (observe fuel next).map fun p => (p.1 + 1, p.2)

def check (name : String) (xs : List ℕ) (expected : ℕ) : IO Unit := do
  let raw := input xs
  match observe 100000 (initList computer raw) with
  | none => throw (IO.userError (name ++ ": finite-machine execution did not halt"))
  | some (time, ending) =>
    unless ending.stk .chosen == encodeNat expected do
      throw (IO.userError (name ++ ": wrong canonical median word"))
    unless (Stack.enumList.all fun k => k == Stack.chosen || (ending.stk k).isEmpty) do
      throw (IO.userError (name ++ ": a work stack was not cleared"))
    unless time ≤ timeBound raw.length do
      throw (IO.userError (name ++ ": transition bound exceeded"))
    IO.println (name ++ ": actual finite machine halted in " ++ toString time ++ " transitions")

#eval check "empty list" [] 0
#eval check "zero observation" [0] 0
#eval check "even upper median" [9, 0] 9
#eval check "repeated observations and ties" [7, 2, 7, 0] 7
#eval check "zero majority" [0, 0, 5, 0] 0
#eval check "mixed odd length" [14, 1, 9, 9, 3] 9
#eval check "descending even length" [10, 8, 6, 4, 2, 0] 6
#eval check "different binary widths" [65536, 0, 31, 32] 32

end Counting.Algorithm.KarpLubyRequest.Median.Clients
