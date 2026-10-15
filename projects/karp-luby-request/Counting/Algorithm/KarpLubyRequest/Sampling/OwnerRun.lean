import Counting.Algorithm.KarpLubyRequest.Sampling.OwnerStages
import Counting.Algorithm.KarpLubyRequest.Sampling.TotalMassRun

/-! # Complete actual prefix-ownership scan with every assignment copy charged -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Owner
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

/-- The tail remaining after an early rejection is retained for caller cleanup. -/
def remaining : List RowSemantics.Cells → List Bool → List RowSemantics.Cells
  | [], _ => []
  | row :: rest, assignment =>
      if RowEval.value row assignment then rest else remaining rest assignment

def answer (rows : List RowSemantics.Cells) (assignment : List Bool) : Bool :=
  !(rows.any (fun row => RowEval.value row assignment))

def runTime : List RowSemantics.Cells → List Bool → ℕ
  | [], _ => 1
  | row :: rest, assignment =>
      5 * row.length + 2 * assignment.length + 7 +
        if RowEval.value row assignment then 0 else runTime rest assignment

theorem run_exact (rows : List RowSemantics.Cells) (assignment : List Bool)
    (hlen : ∀ row ∈ rows, row.length = assignment.length) :
    RunsExactly computer.step (config 0 (Dense.CellCodec.rows rows) [] assignment [] [])
      (finished (answer rows assignment) (Dense.CellCodec.rows (remaining rows assignment)) assignment)
      (runTime rows assignment) := by
  induction rows with
  | nil =>
    simpa only [answer, List.any_nil, Bool.not_false, remaining, Dense.CellCodec.rows_nil,
      runTime] using runsExactly_one (empty_step assignment)
  | cons row rest ih =>
    have hr := hlen row (by simp)
    have ht : ∀ row ∈ rest, row.length = assignment.length := fun row hm => hlen row (by simp [hm])
    have hs := test_row row (Dense.CellCodec.rows rest) assignment hr.symm
    cases h : RowEval.value row assignment with
    | true =>
      rw [h] at hs
      have he := hs.trans (runsExactly_one (reject_step (Dense.CellCodec.rows rest) assignment))
      convert he using 1 <;> simp only [Dense.CellCodec.rows_cons, runTime, answer, remaining, h,
        List.any_cons, Bool.true_or, Bool.not_true, ↓reduceIte, Nat.add_zero,
        Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] <;> omega
    | false =>
      rw [h] at hs
      have he := (hs.trans (runsExactly_one (continue_step (Dense.CellCodec.rows rest) assignment))).trans (ih ht)
      convert he using 1 <;> simp only [Dense.CellCodec.rows_cons, runTime, answer, remaining, h,
        List.any_cons, Bool.false_or, ↓reduceIte, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc, Bool.false_eq_true] <;> omega

theorem time_bound (rows : List RowSemantics.Cells) (assignment : List Bool)
    (hlen : ∀ row ∈ rows, row.length = assignment.length) :
    runTime rows assignment ≤ rows.length * (7 * assignment.length + 7) + 1 := by
  induction rows with
  | nil => simp only [runTime, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons row rest ih =>
    have hr := hlen row (by simp)
    have ht := ih (fun row hm => hlen row (by simp [hm]))
    simp only [runTime, List.length_cons, hr]
    split_ifs <;> nlinarith

theorem input_time_bound (rows : List RowSemantics.Cells) (assignment : List Bool)
    (hlen : ∀ row ∈ rows, row.length = assignment.length) :
    runTime rows assignment ≤
      8 * ((Dense.CellCodec.rows rows).length + assignment.length + 1)^2 := by
  have ht := time_bound rows assignment hlen
  have hn := TotalMass.count_le_input rows
  have hm := Nat.mul_le_mul_right (7 * assignment.length + 7) hn
  nlinarith

/-- Literal evaluation agrees with the original stored assignment, without any
restriction on duplicated clauses or on assignment values. -/
theorem answer_original (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (a : DNF.Assignment n) :
    answer rows (List.ofFn a) =
      !(rows.map (DenseNormalization.denote n)).any (fun row => DNF.evalClause row a) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have hr := hlen row (by simp)
    have ht := ih (fun row hm => hlen row (by simp [hm]))
    have hv : RowEval.value row (List.ofFn a) = DNF.evalClause (DenseNormalization.denote n row) a := by
      subst n
      exact RowEval.value_original row a
    simp only [answer, List.any_cons, List.map_cons, hv, Bool.not_or] at *
    rw [ht]

theorem primitive_cost (rows : List RowSemantics.Cells) (assignment : List Bool)
    (hlen : ∀ row ∈ rows, row.length = assignment.length) :
    (Primitive.run program (runTime rows assignment)
      (some (config 0 (Dense.CellCodec.rows rows) [] assignment [] []))).2 =
      some (finished (answer rows assignment) (Dense.CellCodec.rows (remaining rows assignment)) assignment) ∧
    (Primitive.run program (runTime rows assignment)
      (some (config 0 (Dense.CellCodec.rows rows) [] assignment [] []))).1 ≤
      64 * ((Dense.CellCodec.rows rows).length + assignment.length + 1)^2 := by
  have h := Primitive.execution_cost program 8 statement_budget _ _ _ (run_exact rows assignment hlen)
  refine ⟨h.1, h.2.trans ?_⟩
  have ht := input_time_bound rows assignment hlen
  nlinarith

end Counting.Algorithm.KarpLubyRequest.Sampling.Owner
