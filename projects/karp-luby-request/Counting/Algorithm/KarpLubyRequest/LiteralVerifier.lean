import Counting.Algorithm.KarpLubyRequest.Verifier
import Counting.Algorithm.KarpLubyRequest.LiteralFields

/-!
# Literal validation with a reusable empty-workspace return

This caller uses the literal parser's proven actual instructions, then physically
clears the singleton polarity and remaining copied variable suffix. Those clears
are charged. The original variable word remains unchanged, including unused
variables and arbitrary bit patterns accepted by the unary input codec.
-/
namespace Counting.Algorithm.KarpLubyRequest.LiteralVerifier
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing

abbrev Stack := Fin 6
abbrev Label := Fin 15

def labels : LiteralFields.Labels Label := ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12⟩

def program (label : Label) : Stmt Stack Label Bool :=
  if label = 0 then Frame.scanStmt 0 3 0 1 12
  else if label = 1 then copyMoveStmt 3 1 1 2
  else if label = 2 then RationalFields.singletonStmt 0 3 12
  else if label = 3 then copyMoveStmt 1 3 3 4
  else if label = 4 then NaturalWords.highestStmt 3 2 5
  else if label = 5 then copyMoveStmt 3 2 5 6
  else if label = 6 then copyMoveStmt 5 3 6 7
  else if label = 7 then copyRestoreStmt 5 4 3 7 8
  else if label = 8 then BoundedIndex.checkStmt 4 2 9 11 12
  else if label = 9 then CountedList.Counter.decrementStmt 2 3 9 10
  else if label = 10 then copyMoveStmt 3 2 10 8
  else if label = 11 then clearStmt 0 11 13
  else if label = 12 then .load (fun _ => (none, false)) .halt
  else if label = 13 then clearStmt 4 13 14
  else .load (fun _ => (none, true)) .halt

theorem executes : LiteralFields.Executes (TM2.step program) LiteralFields.localStacks labels := by
  constructor
  · intro state stk; rfl
  · intro state stk; rfl
  · intro state stk; rfl
  · constructor <;> intro state stk <;> rfl
  · intro state stk; rfl
  · intro state stk; rfl
  · constructor <;> intro state stk <;> rfl

theorem statement_budget (label : Label) : TM2Cost.budget (program label) ≤ 10 := by
  fin_cases label <;> decide

def tapes (raw unary original : List Bool) : Stack → List Bool :=
  LiteralFields.tapes LiteralFields.localStacks (fun _ => []) raw [] [] [] unary original

@[simp] theorem tapes_initial (raw original : List Bool) :
    tapes raw [] original = verifierTapes (0 : Stack) 5 raw original := by
  funext k; fin_cases k <;> rfl

private theorem clear_polarity (polarity : Bool) (unary original : List Bool) :
    RunsExactly (TM2.step program) (cfg (11 : Label) false (tapes [polarity] unary original))
      (cfg 13 false (tapes [] unary original)) 2 := by
  have h := clear_exact (TM2.step program) (0 : Stack) (11 : Label) 13
    (by intro state stk; rfl) false (tapes [polarity] unary original)
  have he : Function.update (tapes [polarity] unary original) 0 [] = tapes [] unary original := by
    funext k; fin_cases k <;> rfl
  change RunsExactly _ _ _ 2 at h
  simpa only [he] using h

private theorem clear_unary (unary original : List Bool) :
    RunsExactly (TM2.step program) (cfg (13 : Label) false (tapes [] unary original))
      (cfg 14 false (tapes [] [] original)) (unary.length + 1) := by
  have h := clear_exact (TM2.step program) (4 : Stack) (13 : Label) 14
    (by intro state stk; rfl) false (tapes [] unary original)
  have he : Function.update (tapes [] unary original) 4 [] = tapes [] [] original := by
    funext k; fin_cases k <;> rfl
  change RunsExactly _ _ _ (unary.length + 1) at h
  simpa only [he] using h

/-- All-input execution; workspace cleanup only follows a successfully parsed
literal, and is itself part of the bounded machine run. -/
theorem run (raw original : List Bool) :
    ∃ (ending : Stack → List Bool) (time : ℕ),
      time ≤ LiteralFields.timeBound raw.length original.length + original.length + 4 ∧
      RunsExactly (TM2.step program)
        (cfg (0 : Label) false (verifierTapes (0 : Stack) 5 raw original))
        (⟨none, (none, (LiteralFields.separate original.length raw).isSome), ending⟩ : Cfg Stack Label Bool) time ∧
      ((LiteralFields.separate original.length raw).isSome = true →
        ending = verifierTapes (0 : Stack) 5 [] original) := by
  cases hs : LiteralFields.separate original.length raw with
  | none =>
    obtain ⟨ending, time, ht, hr⟩ := LiteralFields.terminates (TM2.step program)
      LiteralFields.localStacks labels executes false (fun _ => []) raw original
    have hr' : RunsExactly (TM2.step program)
        (cfg (0 : Label) false (verifierTapes (0 : Stack) 5 raw original))
        (cfg 12 false ending) time := by
      rw [← tapes_initial]
      simpa only [hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, labels, tapes] using hr
    refine ⟨ending, 1 + time, by omega, ?_, by simp [hs]⟩
    simpa only [hs, Option.isSome_none] using
      hr'.trans (runsExactly_one (show TM2.step program (cfg (12 : Label) false ending) =
        some (⟨none, (none, false), ending⟩ : Cfg Stack Label Bool) from rfl))
  | some f =>
    obtain ⟨time, ht, hr⟩ := LiteralFields.accepts (TM2.step program)
      LiteralFields.localStacks labels executes false (fun _ => []) raw original f hs
    have hr' : RunsExactly (TM2.step program)
        (cfg (0 : Label) false (verifierTapes (0 : Stack) 5 raw original))
        (cfg 11 false (tapes [f.polarity] (original.drop (decodeNat f.index + 1)) original)) time := by
      rw [← tapes_initial]
      simpa only [labels, tapes] using hr
    have hc := clear_polarity f.polarity (original.drop (decodeNat f.index + 1)) original
    have hd := clear_unary (original.drop (decodeNat f.index + 1)) original
    have hh := runsExactly_one (show TM2.step program (cfg (14 : Label) false (tapes [] [] original)) =
      some (⟨none, (none, true), tapes [] [] original⟩ : Cfg Stack Label Bool) from rfl)
    refine ⟨tapes [] [] original, 1 + ((original.drop (decodeNat f.index + 1)).length + 1 +
      (2 + time)), ?_, ?_, by simp⟩
    · unfold LiteralFields.timeBound; simp only [List.length_drop]; omega
    · simpa only [hs, Option.isSome_some] using ((hr'.trans hc).trans hd).trans hh

def bound (m v : ℕ) := LiteralFields.timeBound m v + v + 4

theorem bound_mono {m n v w : ℕ} (hm : m ≤ n) (hv : v ≤ w) : bound m v ≤ bound n w := by
  unfold bound LiteralFields.timeBound
  have hp := Nat.mul_le_mul (by omega : v + 1 ≤ w + 1) (by omega : 2 * m + 5 ≤ 2 * n + 5)
  omega

/-- Fully instantiated actual source machine for the generic list compiler. -/
def verifier : Verifier Stack Label where
  input := 0
  ambient := 5
  distinct := by decide
  main := 0
  program := program
  accepts raw original := (LiteralFields.separate original.length raw).isSome
  bound := bound
  monotone := bound_mono
  budget := 10
  statement_budget := statement_budget
  run := run

end Counting.Algorithm.KarpLubyRequest.LiteralVerifier
