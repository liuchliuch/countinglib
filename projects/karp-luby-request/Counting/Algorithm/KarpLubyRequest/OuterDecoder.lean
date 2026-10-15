import Counting.Algorithm.KarpLubyRequest.Contract
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-!
# One finite caller for the three outer request fields

The unchanged problem, accuracy, and confidence words are materialized by three
successive calls to H1's canonical returning framing primitive. Every call keeps
the earlier fields and remaining tape on actual Boolean stacks. The two return
labels expose success or failure to the next request stage; no parser callback
is installed as a machine instruction.
-/
namespace Counting.Algorithm.KarpLubyRequest.OuterDecoder

open Turing Computability
open Holant.Complexity.StackProtocol
open Counting.Algorithm.KarpLuby
open Holant.Complexity.GraphPreprocessing

abbrev Stack := Fin 5
abbrev Label := Fin 8
abbrev Config := Cfg Stack Label Unit
abbrev Statement := Stmt Stack Label Unit

def destination (i : Fin 3) : Stack := ⟨i.val + 1, by omega⟩
def scanLabel (i : Fin 3) : Label := ⟨2 * i.val, by omega⟩
def restoreLabel (i : Fin 3) : Label := ⟨2 * i.val + 1, by omega⟩
def nextLabel (i : Fin 3) : Label := ⟨2 * i.val + 2, by omega⟩

/-- Five binary stacks; eight labels; three possible scratch-register states. -/
def program (label : Label) : Statement :=
  if label = 0 then Frame.scanStmt 0 4 0 1 7
  else if label = 1 then copyMoveStmt 4 1 1 2
  else if label = 2 then Frame.scanStmt 0 4 2 3 7
  else if label = 3 then copyMoveStmt 4 2 3 4
  else if label = 4 then Frame.scanStmt 0 4 4 5 7
  else if label = 5 then copyMoveStmt 4 3 5 6
  else .halt

abbrev computer : FinTM2 where
  K := Stack
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label
  main := 0
  σ := Option Bool × Unit
  initialState := (none, ())
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) :=
  inferInstanceAs (Fintype Bool)

theorem scan_executes (i : Fin 3) : ExecutesAt computer.step (scanLabel i)
    (Frame.scanStmt 0 4 (scanLabel i) (restoreLabel i) 7) := by
  fin_cases i <;> intro state stk <;> rfl

theorem restore_executes (i : Fin 3) : ExecutesAt computer.step (restoreLabel i)
    (copyMoveStmt 4 (destination i) (restoreLabel i) (nextLabel i)) := by
  fin_cases i <;> intro state stk <;> rfl

theorem statement_budget (label : Label) : Holant.Complexity.TM2Cost.budget (program label) ≤ 8 := by
  fin_cases label <;> decide

/-- Each payload is extracted into its own field stack; arbitrary unrelated
field stacks are preserved by the canonical returning primitive. -/
theorem field_exact (i : Fin 3) (frame : Stack → List Bool)
    (word suffix output : List Bool) :
    RunsExactly computer.step
      (cfg (scanLabel i) () (tapes3 frame 0 (destination i) 4
        (Encoding.frame word ++ suffix) output []))
      (cfg (nextLabel i) () (tapes3 frame 0 (destination i) 4 suffix (word ++ output) []))
      (2 * (word.length + 1)) := by
  rw [Contract.frame_eq]
  exact Frame.extract_exact 0 (destination i) 4
    (by fin_cases i <;> decide) (by decide) (by fin_cases i <;> decide)
    computer.step (scanLabel i) (restoreLabel i) (nextLabel i) 7
    (scan_executes i) (restore_executes i) () frame word suffix output

/-- The raw stack is also the final tape suffix; the scratch stack is last. -/
def tapes (raw problem epsilon delta scratch : List Bool) : Stack → List Bool :=
  ![raw, problem, epsilon, delta, scratch]

@[simp] theorem tapes_first (raw p e d t a b c : List Bool) :
    tapes3 (tapes raw p e d t) 0 1 4 a b c = tapes a b e d c := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem tapes_second (raw p e d t a b c : List Bool) :
    tapes3 (tapes raw p e d t) 0 2 4 a b c = tapes a p b d c := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem tapes_third (raw p e d t a b c : List Bool) :
    tapes3 (tapes raw p e d t) 0 3 4 a b c = tapes a p e b c := by
  funext k
  fin_cases k <;> rfl

theorem first_exact (p rest e d : List Bool) :
    RunsExactly computer.step (cfg 0 () (tapes (Encoding.frame p ++ rest) [] e d []))
      (cfg 2 () (tapes rest p e d [])) (2 * (p.length + 1)) := by
  simpa [scanLabel, nextLabel, destination] using
    field_exact (0 : Fin 3) (tapes [] [] e d []) p rest []

theorem second_exact (e rest p d : List Bool) :
    RunsExactly computer.step (cfg 2 () (tapes (Encoding.frame e ++ rest) p [] d []))
      (cfg 4 () (tapes rest p e d [])) (2 * (e.length + 1)) := by
  simpa [scanLabel, nextLabel, destination] using
    field_exact (1 : Fin 3) (tapes [] p [] d []) e rest []

theorem third_exact (d rest p e : List Bool) :
    RunsExactly computer.step (cfg 4 () (tapes (Encoding.frame d ++ rest) p e [] []))
      (cfg 6 () (tapes rest p e d [])) (2 * (d.length + 1)) := by
  simpa [scanLabel, nextLabel, destination] using
    field_exact (2 : Fin 3) (tapes [] p e [] []) d rest []

@[simp] theorem cfg_init (raw : List Bool) :
    cfg (0 : Label) () (tapes raw [] [] [] []) = initList computer raw := by
  unfold cfg tapes initList
  congr 1
  funext k
  fin_cases k <;> rfl

/-- One actual execution composes all three field extractors in order. -/
theorem split_join_exact (f : Contract.Fields) :
    RunsExactly computer.step (initList computer (Contract.join f))
      (cfg 6 () (tapes f.tape f.problem f.epsilon f.delta []))
      (2 * (f.problem.length + f.epsilon.length + f.delta.length) + 6) := by
  have h0 := first_exact f.problem
    (Encoding.frame f.epsilon ++ (Encoding.frame f.delta ++ f.tape)) [] []
  have h1 := second_exact f.epsilon (Encoding.frame f.delta ++ f.tape) f.problem []
  have h2 := third_exact f.delta f.tape f.problem f.epsilon
  have hr := h0.trans (h1.trans h2)
  have ht : 2 * (f.delta.length + 1) + 2 * (f.epsilon.length + 1) +
      2 * (f.problem.length + 1) =
      2 * (f.problem.length + f.epsilon.length + f.delta.length) + 6 := by omega
  rw [ht] at hr
  simpa [Contract.join, List.append_assoc, cfg_init] using hr

/-- Canonical full requests reach the concrete next-stage stacks without any
assumption about accuracy validity, satisfiability, or the tape length. -/
def requestRun (r : ProgramEncoding.Request) :
    StateTransition.EvalsToInTime computer.step (initList computer (ProgramEncoding.request.encode r))
      (some (cfg 6 () (tapes r.tape (Encoding.input.encode r.problem)
        (Encoding.output.encode r.epsilon) (Encoding.output.encode r.delta) [])))
      (2 * ((Encoding.input.encode r.problem).length +
        (Encoding.output.encode r.epsilon).length + (Encoding.output.encode r.delta).length) + 6) := by
  rw [Contract.request_encode]
  exact (split_join_exact (Contract.encodedFields r)).toTimed

/-- Premature EOF at any field returns failure in finitely many actual steps.
The partial payload stays in scratch for the caller's explicit cleanup stage. -/
theorem field_reject (i : Fin 3) (frame : Stack → List Bool)
    (input output : List Bool) (h : Encoding.unframe input = none) :
    ∃ (produced : List Bool) (time : ℕ), time ≤ input.length + 1 ∧ produced.length ≤ input.length ∧
      RunsExactly computer.step
        (cfg (scanLabel i) () (tapes3 frame 0 (destination i) 4 input output []))
        (cfg 7 () (tapes3 frame 0 (destination i) 4 [] output produced.reverse)) time := by
  rw [Contract.unframe_eq] at h
  simpa only [List.append_nil] using Frame.rejects 0 (destination i) 4
    (by fin_cases i <;> decide) (by decide) computer.step
    (scanLabel i) (restoreLabel i) 7 (scan_executes i) () frame input output [] h

private theorem unframe_prefix {raw word rest : List Bool}
    (h : Encoding.unframe raw = some (word, rest)) :
    raw = Encoding.frame word ++ rest := by
  rw [Contract.unframe_eq] at h
  simpa only [Contract.frame_eq] using (Frame.unframe_some_iff raw word rest).mp h

/-- Every accepted raw word, including noncanonical field codes, materializes
exactly the fields used by the original decoder. -/
def successRun (raw : List Bool) (f : Contract.Fields) (h : Contract.split raw = some f) :
    StateTransition.EvalsToInTime computer.step (initList computer raw)
      (some (cfg 6 () (tapes f.tape f.problem f.epsilon f.delta [])))
      (raw.length + 3) where
  steps := 2 * (f.problem.length + f.epsilon.length + f.delta.length) + 6
  evals_in_steps := by rw [Contract.split_some_raw h]; exact split_join_exact f
  steps_le_m := by have hl := Contract.split_length h; omega

/-- Failure at the first, second, or third field is handled by the same finite
program. Earlier fields and partial scratch are explicit caller data; no cleanup
or deeper field validation is silently included in this bound. -/
theorem malformedRun (raw : List Bool) (h : Contract.split raw = none) :
    ∃ (saved : Stack → List Bool) (time : ℕ), time ≤ raw.length + 3 ∧
      RunsExactly computer.step (initList computer raw) (cfg 7 () saved) time := by
  cases hp : Encoding.unframe raw with
  | none =>
    obtain ⟨produced, time, ht, _, hr⟩ :=
      field_reject (0 : Fin 3) (tapes [] [] [] [] []) raw [] hp
    refine ⟨tapes [] [] [] [] produced.reverse, time, by omega, ?_⟩
    simpa [scanLabel, destination, cfg_init] using hr
  | some p =>
    rcases p with ⟨p, rest⟩
    have hraw := unframe_prefix hp
    have hlen := congrArg List.length hraw
    simp only [List.length_append, Encoding.frame_length] at hlen
    cases he : Encoding.unframe rest with
    | none =>
      obtain ⟨produced, time, ht, _, hr⟩ :=
        field_reject (1 : Fin 3) (tapes [] p [] [] []) rest [] he
      have hf : RunsExactly computer.step (cfg 2 () (tapes rest p [] [] []))
          (cfg 7 () (tapes [] p [] [] produced.reverse)) time := by
        simpa [scanLabel, destination] using hr
      have whole := (first_exact p rest [] []).trans hf
      refine ⟨tapes [] p [] [] produced.reverse, time + 2 * (p.length + 1), by omega, ?_⟩
      simpa only [← hraw, cfg_init] using whole
    | some e =>
      rcases e with ⟨e, rest2⟩
      have hrest := unframe_prefix he
      have hlen2 := congrArg List.length hrest
      simp only [List.length_append, Encoding.frame_length] at hlen2
      cases hd : Encoding.unframe rest2 with
      | none =>
        obtain ⟨produced, time, ht, _, hr⟩ :=
          field_reject (2 : Fin 3) (tapes [] p e [] []) rest2 [] hd
        have hf : RunsExactly computer.step (cfg 4 () (tapes rest2 p e [] []))
            (cfg 7 () (tapes [] p e [] produced.reverse)) time := by
          simpa [scanLabel, destination] using hr
        have first := first_exact p rest [] []
        rw [hrest] at first
        have whole := first.trans ((second_exact e rest2 p []).trans hf)
        refine ⟨tapes [] p e [] produced.reverse,
          time + 2 * (e.length + 1) + 2 * (p.length + 1), by omega, ?_⟩
        simpa only [← hrest, ← hraw, cfg_init] using whole
      | some d => simp [Contract.split, hp, he, hd] at h

/-- The complete outer decoder reaches its appropriate caller continuation on
all raw inputs within a linear transition bound. -/
theorem allInputs (raw : List Bool) :
    ∃ (saved : Stack → List Bool) (time : ℕ), time ≤ raw.length + 3 ∧
      RunsExactly computer.step (initList computer raw)
        (cfg (if (Contract.split raw).isSome then 6 else 7) () saved) time ∧
      ∀ f, Contract.split raw = some f → saved = tapes f.tape f.problem f.epsilon f.delta [] := by
  cases h : Contract.split raw with
  | none =>
    obtain ⟨saved, time, ht, hr⟩ := malformedRun raw h
    refine ⟨saved, time, ht, ?_, ?_⟩
    · simpa only [h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using hr
    · intro f hf; cases hf
  | some f =>
    refine ⟨tapes f.tape f.problem f.epsilon f.delta [],
      2 * (f.problem.length + f.epsilon.length + f.delta.length) + 6,
      by have hl := Contract.split_length h; omega, ?_, ?_⟩
    · simpa only [Contract.split_some_raw h, h, Option.isSome_some, ↓reduceIte] using
        split_join_exact f
    · intro f' hf
      have he : f = f' := Option.some.inj hf
      subst f'
      rfl

/-- Both continuations really halt in the bundled standalone program. A larger
request caller replaces them with the next validation or rejection block. -/
theorem return_halts (good : Bool) (saved : Stack → List Bool) :
    computer.step (cfg (if good then 6 else 7) () saved) =
      some (⟨none, (none, ()), saved⟩ : Config) := by
  cases good <;> rfl

/-- Actual all-input halting, with every field and failed scratch remaining in
its disclosed stack. This is not a serialized request-value output theorem. -/
theorem terminates (raw : List Bool) :
    ∃ (saved : Stack → List Bool) (time : ℕ), time ≤ raw.length + 4 ∧
      RunsExactly computer.step (initList computer raw)
        (⟨none, (none, ()), saved⟩ : Config) time := by
  obtain ⟨saved, time, ht, hr, _⟩ := allInputs raw
  refine ⟨saved, 1 + time, by omega, ?_⟩
  exact hr.trans (runsExactly_one (return_halts (Contract.split raw).isSome saved))

end Counting.Algorithm.KarpLubyRequest.OuterDecoder
