import Counting.Algorithm.KarpLubyRequest.Preamble
import Counting.Algorithm.KarpLubyRequest.Returning

/-!
# A real request caller for the explicit variable header

The complete preamble is inlined through the canonical returning compiler. Its
finite status bit dispatches to rejection or a real H1 frame extractor operating
on the already materialized problem stack. Every bit pattern in the unary header
is accepted: R1's decoder uses only its length, not an all-true test. The formula
body, both rational fields, and fair-bit tape survive on their actual stacks.
-/
namespace Counting.Algorithm.KarpLubyRequest.ProblemHeader

open Turing Computability
open Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby

structure Fields where
  variableWord : List Bool
  formula : List Bool
  epsilon : RationalFields.Fields
  delta : RationalFields.Fields
  tape : List Bool
  deriving DecidableEq

def separate (raw : List Bool) : Option Fields := do
  let f ← Preamble.separate raw
  let (variableWord, formula) ← Encoding.unframe f.problem
  return ⟨variableWord, formula, f.epsilon, f.delta, f.tape⟩

def validate (f : Fields) : Option ProgramEncoding.Request := do
  let formula ← (Encoding.formula f.variableWord.length).decode f.formula
  return ⟨⟨f.variableWord.length, formula⟩, RationalFields.value f.epsilon,
    RationalFields.value f.delta, f.tape⟩

private theorem unary_decode (raw : List Bool) : Encoding.unaryNat.decode raw = some raw.length := rfl

/-- No extra condition is imposed on the unary header's bit values. -/
theorem decode_eq (raw : List Bool) :
    (separate raw).bind validate = ProgramEncoding.request.decode raw := by
  rw [← Preamble.decode_eq]
  cases hs : Preamble.separate raw with
  | none => simp [separate, hs]
  | some f =>
    cases hu : Encoding.unframe f.problem with
    | none => simp [separate, validate, Preamble.validate, Encoding.input, hs, hu]
    | some p =>
      rcases p with ⟨variableWord, formula⟩
      simp [separate, validate, Preamble.validate, Encoding.input, unary_decode, hs, hu,
        Option.bind_assoc]

abbrev Stack := Preamble.Stack ⊕ Fin 1
abbrev Label := Preamble.Label ⊕ Fin 5
abbrev Config := Cfg Stack Label Bool
abbrev Statement := Stmt Stack Label Bool

def source : Stack := .inl 1
def destination : Stack := .inr 0
def temporary : Stack := .inl 4

/-- Extra labels are dispatch, scan, restore, success, and failure. -/
def outside (label : Fin 5) : Statement :=
  if label = 0 then .branch (fun state => state.2)
    (.goto (fun _ => .inr 1)) (.goto (fun _ => .inr 4))
  else if label = 1 then Frame.scanStmt source temporary (.inr 1) (.inr 2) (.inr 4)
  else if label = 2 then copyMoveStmt temporary destination (.inr 2) (.inr 3)
  else if label = 3 then .halt
  else .load (fun _ => (none, false)) .halt

abbrev computer : FinTM2 :=
  Returning.computer 0 1 0 (none, false) (0 : Fin 5) Preamble.program outside

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) :=
  inferInstanceAs (Fintype Bool)

def lift (stk : Preamble.Stack → List Bool) (variableWord : List Bool) : Stack → List Bool :=
  Sum.elim stk (fun _ => variableWord)

theorem statement_budget (label : Label) : TM2Cost.budget (computer.m label) ≤ 10 := by
  cases label with
  | inl label => simpa only [computer, Returning.computer, Returning.program,
      Returning.budget_block] using Preamble.statement_budget label
  | inr label => fin_cases label <;> decide

theorem initial (raw : List Bool) :
    Returning.cfg (0 : Fin 5) (initList Preamble.computer raw) (fun _ : Fin 1 => []) =
      initList computer raw := by
  unfold Returning.cfg initList
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

/-- The earlier complete source machine runs inside this larger actual program;
its halt becomes the dispatch continuation without increasing its transition count. -/
theorem preamble_run (raw : List Bool) :
    ∃ (saved : Preamble.Stack → List Bool) (time : ℕ), time ≤ 2 * raw.length + 20 ∧
      RunsExactly computer.step (initList computer raw)
        (cfg (.inr 0) (Preamble.separate raw).isSome (lift saved [])) time ∧
      ∀ f, Preamble.separate raw = some f → saved = Preamble.resultTapes f := by
  obtain ⟨saved, time, ht, hr, hf⟩ := Preamble.allInputs raw
  have haltRun := hr.trans
    (runsExactly_one (Preamble.return_halts (Preamble.separate raw).isSome saved))
  have lifted := Returning.run_program (0 : Fin 5) Preamble.program outside
    (initList Preamble.computer raw)
    (⟨none, (none, (Preamble.separate raw).isSome), saved⟩ : Preamble.Config)
    (fun _ : Fin 1 => []) (1 + time) haltRun
  refine ⟨saved, 1 + time, by omega, ?_, hf⟩
  rw [initial] at lifted
  exact lifted

theorem dispatch_step (good : Bool) (stk : Stack → List Bool) :
    computer.step (cfg (.inr 0) good stk) =
      some (cfg (.inr (if good then 1 else 4)) good stk) := by
  cases good <;> rfl

theorem scan_executes : ExecutesAt computer.step (.inr 1)
    (Frame.scanStmt source temporary (.inr 1) (.inr 2) (.inr 4)) := by
  intro state stk
  rfl

theorem restore_executes : ExecutesAt computer.step (.inr 2)
    (copyMoveStmt temporary destination (.inr 2) (.inr 3)) := by
  intro state stk
  rfl

/-- Variable bits are retained verbatim; only the residual formula replaces the
old problem word. Every other stack still contains the computed preamble result. -/
def resultTapes (f : Preamble.Fields) (variableWord formula : List Bool) : Stack → List Bool :=
  Function.update (lift (Preamble.resultTapes f) variableWord) source formula

@[simp] theorem tapes_start (f : Preamble.Fields) :
    tapes3 (lift (Preamble.resultTapes f) []) source destination temporary f.problem [] [] =
      lift (Preamble.resultTapes f) [] := by
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

@[simp] theorem tapes_result (f : Preamble.Fields) (variableWord formula : List Bool) :
    tapes3 (lift (Preamble.resultTapes f) []) source destination temporary formula variableWord [] =
      resultTapes f variableWord formula := by
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

/-- Real parsing starts on the materialized problem, not on a caller-supplied
variable count. All variable-header bit patterns remain legal. -/
theorem header_exact (f : Preamble.Fields) (variableWord formula : List Bool)
    (h : Encoding.unframe f.problem = some (variableWord, formula)) :
    RunsExactly computer.step (cfg (.inr 1) true (lift (Preamble.resultTapes f) []))
      (cfg (.inr 3) true (resultTapes f variableWord formula)) (2 * (variableWord.length + 1)) := by
  have hp : f.problem = Holant.Algebraic.frame variableWord ++ formula := by
    rw [Contract.unframe_eq] at h
    exact (Frame.unframe_some_iff _ _ _).mp h
  have hr := Frame.extract_exact source destination temporary (by decide) (by decide) (by decide)
    computer.step (.inr 1) (.inr 2) (.inr 3) (.inr 4)
    scan_executes restore_executes true (lift (Preamble.resultTapes f) []) variableWord formula []
  rw [← hp] at hr
  simp only [List.append_nil] at hr
  rw [tapes_start, tapes_result] at hr
  exact hr

/-- Actual sequential handoff from the complete original raw request. -/
theorem accepts (raw : List Bool) (f : Preamble.Fields) (variableWord formula : List Bool)
    (hs : Preamble.separate raw = some f)
    (hu : Encoding.unframe f.problem = some (variableWord, formula)) :
    ∃ time, time ≤ 2 * raw.length + 2 * variableWord.length + 23 ∧
      RunsExactly computer.step (initList computer raw)
        (cfg (.inr 3) true (resultTapes f variableWord formula)) time := by
  obtain ⟨saved, time, ht, hr, hf⟩ := preamble_run raw
  have he := hf f hs
  subst saved
  simp only [hs, Option.isSome_some] at hr
  have dispatch := runsExactly_one (dispatch_step true (lift (Preamble.resultTapes f) []))
  simp only [↓reduceIte] at dispatch
  refine ⟨2 * (variableWord.length + 1) + (1 + time), by omega, ?_⟩
  exact (hr.trans dispatch).trans (header_exact f variableWord formula hu)


/-- Physical problem length is charged by the unchanged outer request code. -/
theorem problem_length_le (raw : List Bool) (f : Preamble.Fields)
    (h : Preamble.separate raw = some f) : f.problem.length ≤ raw.length := by
  unfold Preamble.separate at h
  cases ho : Contract.split raw with
  | none => simp [ho] at h
  | some outer =>
    cases he : RationalFields.separate outer.epsilon with
    | none => simp [ho, he] at h
    | some e =>
      cases hd : RationalFields.separate outer.delta with
      | none => simp [ho, he, hd] at h
      | some d =>
        simp [ho, he, hd] at h
        subst f
        have hl := Contract.split_length ho
        dsimp only
        omega

theorem header_rejects (f : Preamble.Fields)
    (h : Encoding.unframe f.problem = none) :
    ∃ (saved : Stack → List Bool) (time : ℕ), time ≤ f.problem.length + 1 ∧
      RunsExactly computer.step (cfg (.inr 1) true (lift (Preamble.resultTapes f) []))
        (cfg (.inr 4) true saved) time := by
  rw [Contract.unframe_eq] at h
  obtain ⟨produced, time, ht, _, hr⟩ := Frame.rejects source destination temporary
    (by decide) (by decide) computer.step (.inr 1) (.inr 2) (.inr 4) scan_executes true
    (lift (Preamble.resultTapes f) []) f.problem [] [] h
  refine ⟨tapes3 (lift (Preamble.resultTapes f) []) source destination temporary
    [] [] produced.reverse, time, ht, ?_⟩
  rw [tapes_start] at hr
  simpa only [List.append_nil] using hr

theorem success_halts (stk : Stack → List Bool) :
    computer.step (cfg (.inr 3) true stk) = some (⟨none, (none, true), stk⟩ : Config) := rfl

theorem failure_halts (memory : Bool) (stk : Stack → List Bool) :
    computer.step (cfg (.inr 4) memory stk) = some (⟨none, (none, false), stk⟩ : Config) := rfl

/-- The inlined request program reaches a real halt on every raw input. This
bound includes the preamble, dispatch, variable framing, and final halt; DNF
lists and literal ranges are the remaining formula-body validation. -/
theorem terminates (raw : List Bool) :
    ∃ (saved : Stack → List Bool) (time : ℕ), time ≤ 3 * raw.length + 24 ∧
      RunsExactly computer.step (initList computer raw)
        (⟨none, (none, (separate raw).isSome), saved⟩ : Config) time := by
  obtain ⟨saved, time, ht, hr, hf⟩ := preamble_run raw
  cases hs : Preamble.separate raw with
  | none =>
    simp only [hs, Option.isSome_none] at hr
    have dispatch := runsExactly_one (dispatch_step false (lift saved []))
    simp only [Bool.false_eq_true, ↓reduceIte] at dispatch
    have run := (hr.trans dispatch).trans (runsExactly_one (failure_halts false (lift saved [])))
    refine ⟨lift saved [], 1 + (1 + time), by omega, ?_⟩
    simpa [separate, hs] using run
  | some f =>
    have he := hf f hs
    subst saved
    simp only [hs, Option.isSome_some] at hr
    have dispatch := runsExactly_one (dispatch_step true (lift (Preamble.resultTapes f) []))
    simp only [↓reduceIte] at dispatch
    have firstRun := hr.trans dispatch
    have hlen := problem_length_le raw f hs
    cases hu : Encoding.unframe f.problem with
    | none =>
      obtain ⟨ending, duration, hd, hrun⟩ := header_rejects f hu
      have run := (firstRun.trans hrun).trans (runsExactly_one (failure_halts true ending))
      refine ⟨ending, 1 + (duration + (1 + time)), by omega, ?_⟩
      simpa [separate, hs, hu] using run
    | some pair =>
      rcases pair with ⟨variableWord, formula⟩
      have hu' := hu
      rw [Contract.unframe_eq] at hu'
      have hp := (Frame.unframe_some_iff _ _ _).mp hu'
      have hl := congrArg List.length hp
      simp only [← Contract.frame_eq, List.length_append, Encoding.frame_length] at hl
      have run := (firstRun.trans (header_exact f variableWord formula hu)).trans
        (runsExactly_one (success_halts (resultTapes f variableWord formula)))
      refine ⟨resultTapes f variableWord formula, 1 + (2 * (variableWord.length + 1) + (1 + time)),
        by omega, ?_⟩
      simpa [separate, hs, hu] using run

end Counting.Algorithm.KarpLubyRequest.ProblemHeader
