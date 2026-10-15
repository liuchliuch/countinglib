import Counting.Algorithm.KarpLubyRequest.Embedded
import Counting.Algorithm.KarpLubyRequest.Median.Machine
import Holant.Complexity.FixedFieldMachines.FrameEmit

/-! Physical ordered accumulation of group numerators. Stack 0 receives a
canonical numerator and later holds the final median input. Stack 1 contains
reverse framed records, stack 2 is scratch, and stack 3 holds the canonical
number of groups. No unbounded value resides in finite control. -/
namespace Counting.Algorithm.KarpLubyRequest.GroupOutput
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Turing.TM2.Stmt
open Counting.Algorithm.KarpLuby

abbrev Stack := Fin 4
abbrev State := Option Bool × Unit
inductive Label
  | append | reverse | frameMove | delimiter | emit | done
  deriving DecidableEq, Fintype

def program : Label → Stmt Stack Label Unit
  | .append => pop 0 (fun _ bit => (bit, ()))
      (branch (fun v => v.1.isSome)
        (push 1 (fun _ => true) (push 1 (fun v => v.1.getD false)
          (load (fun _ => (none, ())) (goto (fun _ => .append)))))
        (push 1 (fun _ => false) (load (fun _ => (none, ())) halt)))
  | .reverse => copyMoveStmt 1 0 .reverse .frameMove
  | .frameMove => copyMoveStmt 3 2 .frameMove .delimiter
  | .delimiter => FixedFieldMachines.FrameEmit.delimiterStmt 0 .emit
  | .emit => FixedFieldMachines.FrameEmit.emitStmt 2 0 .emit .done
  | .done => halt

/-- This program has two prepared-bank entry labels. The append entry returns
its accumulator on stack 1; the finish entry returns the final word on stack 0. -/
abbrev computer : FinTM2 where
  K := Stack
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label
  main := .append
  σ := State
  initialState := (none, ())
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

def bank (incoming accumulator scratch count : List Bool) : Stack → List Bool :=
  ![incoming, accumulator, scratch, count]

def body (words : List (List Bool)) : List Bool := Encoding.frames words

theorem body_nil : body [] = [] := rfl
theorem body_cons (word : List Bool) (words : List (List Bool)) :
    body (word :: words) = Encoding.frame word ++ body words := rfl

theorem body_append (words tail : List (List Bool)) : body (words ++ tail) = body words ++ body tail := by
  induction words with
  | nil => simp only [List.nil_append, body_nil, List.nil_append]
  | cons word words ih =>
    simp only [List.cons_append, body_cons, ih, List.append_assoc]

/-- Reversed physical storage preserves the original logical occurrence order. -/
def reversed (xs : List ℕ) : List Bool := (body (xs.map encodeNat)).reverse

theorem reverse_frame_nil : (Encoding.frame []).reverse = [false] := rfl

theorem reverse_frame_cons (bit : Bool) (word : List Bool) :
    (Encoding.frame (bit :: word)).reverse = (Encoding.frame word).reverse ++ [bit, true] := by
  change (true :: bit :: Encoding.frame word).reverse = _
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem reversed_append (xs : List ℕ) (a : ℕ) :
    reversed (xs ++ [a]) = (Encoding.frame (encodeNat a)).reverse ++ reversed xs := by
  simp only [reversed, List.map_append, List.map_cons, List.map_nil,
    body_append, body_cons, body_nil, List.append_nil, List.reverse_append]

theorem statement_budget (l : Label) : TM2Cost.budget (program l) ≤ 6 := by
  cases l <;> decide

end Counting.Algorithm.KarpLubyRequest.GroupOutput
