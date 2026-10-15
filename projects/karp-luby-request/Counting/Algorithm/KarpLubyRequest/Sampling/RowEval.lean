import Counting.Algorithm.KarpLubyRequest.Sampling.RowSemantics
import Holant.Complexity.GraphPreprocessing.Primitive

/-!
# Actual evaluation of a dense row on a stored assignment

The machine reads both row symbols and one assignment symbol per coordinate.
It keeps only the current literal and accumulated conjunction in finite control.
In particular, the assignment access is an actual pop and its cost is included.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.RowEval
open Turing Computability Holant.Complexity StackProtocol
open RowSemantics

/-- Pure specification of the physical row/assignment scan. -/
def value : Cells → List Bool → Bool
  | [], _ => true
  | none :: xs, a => value xs a.tail
  | some b :: xs, a => (a.head?.getD false == b) && value xs a.tail

theorem value_original (xs : Cells) (a : Counting.Algorithm.KarpLuby.DNF.Assignment xs.length) :
    value xs (List.ofFn a) = Counting.Algorithm.KarpLuby.DNF.evalClause
      (Counting.Algorithm.KarpLubyMachine.DenseNormalization.denote xs.length xs) a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change value (x :: xs) (List.ofFn a) = Counting.Algorithm.KarpLuby.DNF.evalClause
      (Counting.Algorithm.KarpLubyMachine.DenseNormalization.denote (xs.length + 1) (x :: xs)) a
    dsimp only [Counting.Algorithm.KarpLuby.DNF.evalClause]
    rw [denote_cons_zero, denote_cons_succ, List.ofFn_succ]
    cases x <;> simp only [value, List.tail_cons, List.head?_cons, Option.getD_some, ih]

abbrev Stack := Fin 2
abbrev State := Option Bool × Bool × Bool
def tapes (row assignment : List Bool) : Stack → List Bool := ![row, assignment]
def config (row assignment : List Bool) (acc : Bool) : Cfg Stack Unit (Bool × Bool) :=
  ⟨some (), (none, false, acc), tapes row assignment⟩
def finished (row assignment : List Bool) (acc : Bool) : Cfg Stack Unit (Bool × Bool) :=
  ⟨none, (none, false, acc), tapes row assignment⟩

def program (_ : Unit) : Stmt Stack Unit (Bool × Bool) :=
  .pop 0 (fun v bit => (bit, v.2))
    (.branch (fun v => v.1.isSome)
      (.branch (fun v => v.1.getD false)
        (.pop 0 (fun v bit => (none, bit.getD false, v.2.2))
          (.pop 1 (fun v bit => (bit, v.2))
            (.load (fun v => (none, false, v.2.2 && (v.1.getD false == v.2.1)))
              (.goto (fun _ => ())))))
        (.pop 0 (fun v _ => v)
          (.pop 1 (fun v _ => v)
            (.load (fun v => (none, false, v.2.2)) (.goto (fun _ => ()))))))
      (.load (fun v => (none, false, v.2.2)) .halt))

abbrev computer : FinTM2 where
  K := Stack
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := State
  initialState := (none, false, true)
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

theorem step_free (row assignment : List Bool) (acc : Bool) :
    computer.step (config (false :: false :: row) assignment acc) =
      some (config row assignment.tail acc) := by
  cases assignment <;>
    simp [FinTM2.step, TM2.step, program, config, TM2.stepAux, tapes]
  all_goals congr 2; funext k; fin_cases k <;> rfl

theorem step_fixed (b : Bool) (row assignment : List Bool) (acc : Bool) :
    computer.step (config (true :: b :: row) assignment acc) =
      some (config row assignment.tail (acc && (assignment.head?.getD false == b))) := by
  cases assignment <;>
    simp [FinTM2.step, TM2.step, program, config, TM2.stepAux, tapes]
  all_goals congr 2; funext k; fin_cases k <;> rfl

theorem step_done (assignment : List Bool) (acc : Bool) :
    computer.step (config [] assignment acc) = some (finished [] assignment acc) := by
  simp [FinTM2.step, TM2.step, program, config, finished, TM2.stepAux, tapes]
  congr 2; funext k; fin_cases k <;> rfl

/-- The exact run is valid even on short assignment words, with the displayed
default-false convention. Original assignments have exactly the correct length. -/
theorem scan_exact (xs : Cells) (assignment : List Bool) (acc : Bool) :
    RunsExactly computer.step (config (Dense.CellCodec.encode xs) assignment acc)
      (finished [] (assignment.drop xs.length) (acc && value xs assignment)) (xs.length + 1) := by
  induction xs generalizing assignment acc with
  | nil =>
    simpa only [Dense.CellCodec.encode_nil, List.length_nil, List.drop_zero, value,
      Bool.and_true, Nat.zero_add] using runsExactly_one (step_done assignment acc)
  | cons x xs ih =>
    have hd : assignment.tail.drop xs.length = assignment.drop (xs.length + 1) := by
      cases assignment <;> simp
    cases x with
    | none =>
      simpa only [Dense.CellCodec.encode_cons, Dense.CellCodec.cell, List.cons_append,
        List.nil_append, List.length_cons, value, hd] using
        (runsExactly_one (step_free (Dense.CellCodec.encode xs) assignment acc)).trans
          (ih assignment.tail acc)
    | some b =>
      simpa only [Dense.CellCodec.encode_cons, Dense.CellCodec.cell, List.cons_append,
        List.nil_append, List.length_cons, value, hd, Bool.and_assoc] using
        (runsExactly_one (step_fixed b (Dense.CellCodec.encode xs) assignment acc)).trans
          (ih assignment.tail (acc && (assignment.head?.getD false == b)))

theorem run_original (xs : Cells) (a : Counting.Algorithm.KarpLuby.DNF.Assignment xs.length) :
    RunsExactly computer.step (config (Dense.CellCodec.encode xs) (List.ofFn a) true)
      (finished [] [] (Counting.Algorithm.KarpLuby.DNF.evalClause
        (Counting.Algorithm.KarpLubyMachine.DenseNormalization.denote xs.length xs) a))
      (xs.length + 1) := by
  have h := scan_exact xs (List.ofFn a) true
  have hd : (List.ofFn a).drop xs.length = [] := List.drop_eq_nil_of_le (by simp)
  simpa only [hd, Bool.true_and, value_original] using h

theorem statement_budget (label : Unit) : TM2Cost.budget (program label) ≤ 7 := by
  cases label
  decide

theorem primitive_cost (xs : Cells) (a : Counting.Algorithm.KarpLuby.DNF.Assignment xs.length) :
    (GraphPreprocessing.Primitive.run program (xs.length + 1)
      (some (config (Dense.CellCodec.encode xs) (List.ofFn a) true))).2 =
      some (finished [] [] (Counting.Algorithm.KarpLuby.DNF.evalClause
        (Counting.Algorithm.KarpLubyMachine.DenseNormalization.denote xs.length xs) a)) ∧
    (GraphPreprocessing.Primitive.run program (xs.length + 1)
      (some (config (Dense.CellCodec.encode xs) (List.ofFn a) true))).1 ≤ 7 * (xs.length + 1) :=
  GraphPreprocessing.Primitive.execution_cost program 7 statement_budget _ _ _ (run_original xs a)

end Counting.Algorithm.KarpLubyRequest.Sampling.RowEval
