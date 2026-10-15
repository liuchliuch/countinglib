import Counting.Algorithm.KarpLubyRequest.Output.Machine

set_option maxRecDepth 8192

/-! Literal-code edge cases and executions of the actual output machine. -/
namespace Counting.Algorithm.KarpLubyRequest.Output.Clients
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby
open Program

example : numerator 12 18 = 2 ∧ denominator 12 18 = 3 := by decide
example : numerator 0 17 = 0 ∧ denominator 0 17 = 1 := by decide
example : numerator 17 0 = 0 ∧ denominator 17 0 = 1 := by decide
example : numerator 0 0 = 0 ∧ denominator 0 0 = 1 := by decide
example : Encoding.encodeOutput 0 = [true, true, true, false, true, false, false, true] := rfl
example : Encoding.encodeOutput (1 / 2 : ℚ) =
    [true, true, true, false, true, false, true, true, false, false, true] := by
  change Encoding.encodeOutput (((1 : ℕ) : ℚ) / (2 : ℕ)) = _
  rw [output_eq]
  rfl
example : Fintype.card Stack = 14 := Holant.Complexity.RationalArithmetic.Normalization.stack_count
example : Fintype.card Label = 70 := by decide
example : Fintype.card State = 216 := by decide

/-- A concrete exhaustive enumeration, independent of noncomputable Finset
choice. Its coverage is checked below before it is used for stack cleanup. -/
def stackList : List Stack :=
  [.inl (.inl .input), .inl (.inl .divisor), .inl (.inl .remainder),
    .inl (.inl .divisorRev), .inl (.inl .oldRev), .inl (.inl .trialRev), .inl (.inl .quotient),
    .inl (.inr .saved), .inl (.inr .temp),
    ex .num, ex .den, ex .temp, ex .gcd, ex .stream]

theorem stackList_complete (k : Stack) : k ∈ stackList := by
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [stackList]
    | inr k => cases k <;> simp [stackList]
  | inr k => cases k <;> simp [stackList]

/-- A bounded observer of displayed TM2 transitions; it does not perform the
normalization or serialization itself. -/
def observe : ℕ → computer.Cfg → Option (ℕ × computer.Cfg)
  | 0, c => if c.l.isNone then some (0, c) else none
  | fuel + 1, c =>
    if c.l.isNone then some (0, c)
    else (computer.step c).bind fun next => (observe fuel next).map fun p => (p.1 + 1, p.2)

def check (name : String) (a s : ℕ) (expected : ℚ) : IO Unit := do
  let raw := input a s
  match observe 200000 (initList computer raw) with
  | none => throw (IO.userError (name ++ ": physical output machine did not halt"))
  | some (steps, ending) =>
    unless ending.stk (ex .den) == Encoding.encodeOutput expected do
      throw (IO.userError (name ++ ": final literal R1 codec differs"))
    unless (stackList.all fun k =>
        k == ex .den || (ending.stk k).isEmpty) do
      throw (IO.userError (name ++ ": a physical work stack remains nonempty"))
    unless ending.var == computer.initialState do
      throw (IO.userError (name ++ ": finite registers were not restored"))
    unless steps ≤ timeBound raw.length do
      throw (IO.userError (name ++ ": cubic transition budget exceeded"))
    unless steps == time a s do
      throw (IO.userError (name ++ ": exact source count differs"))
    IO.println (name ++ ": actual output machine halted in " ++ toString steps ++ " transitions")

#eval check "zero numerator" 0 17 0
#eval check "zero denominator" 17 0 0
#eval check "both zero" 0 0 0
#eval check "proper fraction and cancellation" 12 18 (2 / 3)
#eval check "integer after cancellation" 84 7 12
#eval check "coprime unequal widths" 257 16 (257 / 16)
#eval check "unit fraction" 1 2 (1 / 2)
#eval check "equal numerator and denominator" 63 63 1

end Counting.Algorithm.KarpLubyRequest.Output.Clients
