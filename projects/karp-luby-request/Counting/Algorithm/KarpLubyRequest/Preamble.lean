import Counting.Algorithm.KarpLubyRequest.OuterDecoder
import Counting.Algorithm.KarpLubyRequest.RationalFields

/-!
# Connected request framing and rational-field machine

One finite program materializes the three outer fields, validates epsilon, and
then validates delta. The caller retains the problem word and fair-bit tape on
separate stacks throughout. Its success boundary is deliberately before DNF
validation, parameter inequalities, normalization, and estimation. The final finite Boolean status flag survives halting so that H1's
canonical returning compiler can dispatch success or failure in a larger caller.
-/
namespace Counting.Algorithm.KarpLubyRequest.Preamble

open Turing Computability
open Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby

structure Fields where
  problem : List Bool
  epsilon : RationalFields.Fields
  delta : RationalFields.Fields
  tape : List Bool
  deriving DecidableEq

def separate (raw : List Bool) : Option Fields := do
  let f ← Contract.split raw
  let e ← RationalFields.separate f.epsilon
  let d ← RationalFields.separate f.delta
  return ⟨f.problem, e, d, f.tape⟩

/-- DNF decoding is the remaining semantic validator at this stage. -/
def validate (f : Fields) : Option ProgramEncoding.Request := do
  let problem ← Encoding.input.decode f.problem
  return ⟨problem, RationalFields.value f.epsilon, RationalFields.value f.delta, f.tape⟩

/-- Rearranging independent validity checks preserves the original decoder on
all raw requests, including malformed or noncanonical component words. -/
theorem decode_eq (raw : List Bool) :
    (separate raw).bind validate = ProgramEncoding.request.decode raw := by
  rw [← Contract.decode_eq]
  cases hs : Contract.split raw with
  | none => simp [separate, Contract.decode, hs]
  | some f =>
    cases he : RationalFields.separate f.epsilon <;>
      cases hd : RationalFields.separate f.delta <;>
      cases hp : Encoding.input.decode f.problem <;>
      simp [separate, validate, Contract.decode, Contract.validate, hs, he, hd, hp,
        RationalFields.output_decode_eq]

abbrev Stack := Fin 9
abbrev Label := Fin 20
abbrev Config := Cfg Stack Label Bool
abbrev Statement := Stmt Stack Label Bool

/-- raw/tape, problem, epsilon denominator, delta denominator, scratch,
epsilon magnitude and sign, delta magnitude and sign. -/
def tapes (raw p e d tmp em es dm ds : List Bool) : Stack → List Bool :=
  ![raw, p, e, d, tmp, em, es, dm, ds]

def epsilonStacks : RationalFields.Stacks Stack :=
  ⟨![2, 5, 6, 4], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

def deltaStacks : RationalFields.Stacks Stack :=
  ⟨![3, 7, 8, 4], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

def epsilonLabels : RationalFields.Labels Label := ⟨6, 7, 8, 9, 10, 11, 12, 19⟩
def deltaLabels : RationalFields.Labels Label := ⟨12, 13, 14, 15, 16, 17, 18, 19⟩

/-- All instructions act on bounded control and Boolean stack symbols. -/
def program (label : Label) : Statement :=
  if label = 0 then Frame.scanStmt 0 4 0 1 19
  else if label = 1 then copyMoveStmt 4 1 1 2
  else if label = 2 then Frame.scanStmt 0 4 2 3 19
  else if label = 3 then copyMoveStmt 4 2 3 4
  else if label = 4 then Frame.scanStmt 0 4 4 5 19
  else if label = 5 then copyMoveStmt 4 3 5 6
  else if label = 6 then Frame.scanStmt 2 4 6 7 19
  else if label = 7 then copyMoveStmt 4 5 7 8
  else if label = 8 then Frame.scanStmt 5 4 8 9 19
  else if label = 9 then copyMoveStmt 4 6 9 10
  else if label = 10 then RationalFields.singletonStmt 6 11 19
  else if label = 11 then RationalFields.denominatorStmt 2 12 19
  else if label = 12 then Frame.scanStmt 3 4 12 13 19
  else if label = 13 then copyMoveStmt 4 7 13 14
  else if label = 14 then Frame.scanStmt 7 4 14 15 19
  else if label = 15 then copyMoveStmt 4 8 15 16
  else if label = 16 then RationalFields.singletonStmt 8 17 19
  else if label = 17 then RationalFields.denominatorStmt 3 18 19
  else if label = 18 then .load (fun _ => (none, true)) .halt
  else .load (fun _ => (none, false)) .halt

abbrev computer : FinTM2 where
  K := Stack
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label
  main := 0
  σ := Option Bool × Bool
  initialState := (none, false)
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) :=
  inferInstanceAs (Fintype Bool)

theorem statement_budget (label : Label) : TM2Cost.budget (program label) ≤ 10 := by
  fin_cases label <;> decide

theorem epsilon_executes :
    RationalFields.Executes computer.step epsilonStacks epsilonLabels := by
  constructor <;> intro state stk <;> rfl

theorem delta_executes :
    RationalFields.Executes computer.step deltaStacks deltaLabels := by
  constructor <;> intro state stk <;> rfl

@[simp] theorem epsilon_tapes (raw p e d tmp em es dm ds a b c t : List Bool) :
    RationalFields.tapes epsilonStacks (tapes raw p e d tmp em es dm ds) a b c t =
      tapes raw p a d t b c dm ds := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem delta_tapes (raw p e d tmp em es dm ds a b c t : List Bool) :
    RationalFields.tapes deltaStacks (tapes raw p e d tmp em es dm ds) a b c t =
      tapes raw p e a t em es b c := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem tapes_first (raw p e d t em es dm ds a b c : List Bool) :
    tapes3 (tapes raw p e d t em es dm ds) 0 1 4 a b c =
      tapes a b e d c em es dm ds := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem tapes_second (raw p e d t em es dm ds a b c : List Bool) :
    tapes3 (tapes raw p e d t em es dm ds) 0 2 4 a b c =
      tapes a p b d c em es dm ds := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem tapes_third (raw p e d t em es dm ds a b c : List Bool) :
    tapes3 (tapes raw p e d t em es dm ds) 0 3 4 a b c =
      tapes a p e b c em es dm ds := by
  funext k
  fin_cases k <;> rfl

def destination (i : Fin 3) : Stack := ⟨i.val + 1, by omega⟩
def scanLabel (i : Fin 3) : Label := ⟨2 * i.val, by omega⟩
def restoreLabel (i : Fin 3) : Label := ⟨2 * i.val + 1, by omega⟩
def nextLabel (i : Fin 3) : Label := ⟨2 * i.val + 2, by omega⟩

theorem scan_executes (i : Fin 3) : ExecutesAt computer.step (scanLabel i)
    (Frame.scanStmt 0 4 (scanLabel i) (restoreLabel i) 19) := by
  fin_cases i <;> intro state stk <;> rfl

theorem restore_executes (i : Fin 3) : ExecutesAt computer.step (restoreLabel i)
    (copyMoveStmt 4 (destination i) (restoreLabel i) (nextLabel i)) := by
  fin_cases i <;> intro state stk <;> rfl

theorem field_exact (i : Fin 3) (frame : Stack → List Bool)
    (word suffix output : List Bool) :
    RunsExactly computer.step
      (cfg (scanLabel i) false (tapes3 frame 0 (destination i) 4
        (Encoding.frame word ++ suffix) output []))
      (cfg (nextLabel i) false (tapes3 frame 0 (destination i) 4 suffix (word ++ output) []))
      (2 * (word.length + 1)) := by
  rw [Contract.frame_eq]
  exact Frame.extract_exact 0 (destination i) 4
    (by fin_cases i <;> decide) (by decide) (by fin_cases i <;> decide)
    computer.step (scanLabel i) (restoreLabel i) (nextLabel i) 19
    (scan_executes i) (restore_executes i) false frame word suffix output

theorem first_exact (p rest e d : List Bool) :
    RunsExactly computer.step (cfg 0 false (tapes (Encoding.frame p ++ rest) [] e d [] [] [] [] []))
      (cfg 2 false (tapes rest p e d [] [] [] [] [])) (2 * (p.length + 1)) := by
  simpa [scanLabel, nextLabel, destination] using
    field_exact (0 : Fin 3) (tapes [] [] e d [] [] [] [] []) p rest []

theorem second_exact (e rest p d : List Bool) :
    RunsExactly computer.step (cfg 2 false (tapes (Encoding.frame e ++ rest) p [] d [] [] [] [] []))
      (cfg 4 false (tapes rest p e d [] [] [] [] [])) (2 * (e.length + 1)) := by
  simpa [scanLabel, nextLabel, destination] using
    field_exact (1 : Fin 3) (tapes [] p [] d [] [] [] [] []) e rest []

theorem third_exact (d rest p e : List Bool) :
    RunsExactly computer.step (cfg 4 false (tapes (Encoding.frame d ++ rest) p e [] [] [] [] [] []))
      (cfg 6 false (tapes rest p e d [] [] [] [] [])) (2 * (d.length + 1)) := by
  simpa [scanLabel, nextLabel, destination] using
    field_exact (2 : Fin 3) (tapes [] p e [] [] [] [] [] []) d rest []

@[simp] theorem cfg_init (raw : List Bool) :
    cfg (0 : Label) false (tapes raw [] [] [] [] [] [] [] []) = initList computer raw := by
  unfold cfg tapes initList
  congr 1
  funext k
  fin_cases k <;> rfl

theorem outer_exact (f : Contract.Fields) :
    RunsExactly computer.step (initList computer (Contract.join f))
      (cfg 6 false (tapes f.tape f.problem f.epsilon f.delta [] [] [] [] []))
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

/-- Selected stack contents at the connected success continuation. -/
def resultTapes (f : Fields) : Stack → List Bool :=
  tapes f.tape f.problem f.epsilon.denominator f.delta.denominator []
    f.epsilon.magnitude [f.epsilon.negative] f.delta.magnitude [f.delta.negative]

theorem epsilon_accepts (outer : Contract.Fields) (e : RationalFields.Fields)
    (h : RationalFields.separate outer.epsilon = some e) :
    RunsExactly computer.step
      (cfg 6 false (tapes outer.tape outer.problem outer.epsilon outer.delta [] [] [] [] []))
      (cfg 12 false (tapes outer.tape outer.problem e.denominator outer.delta []
        e.magnitude [e.negative] [] [])) (2 * e.magnitude.length + 14) := by
  simpa only [epsilon_tapes, epsilonLabels] using
    RationalFields.accepts computer.step epsilonStacks epsilonLabels epsilon_executes false
      (tapes outer.tape outer.problem [] outer.delta [] [] [] [] []) outer.epsilon e h

theorem delta_accepts (outer : Contract.Fields) (e d : RationalFields.Fields)
    (h : RationalFields.separate outer.delta = some d) :
    RunsExactly computer.step
      (cfg 12 false (tapes outer.tape outer.problem e.denominator outer.delta []
        e.magnitude [e.negative] [] []))
      (cfg 18 false (resultTapes ⟨outer.problem, e, d, outer.tape⟩))
      (2 * d.magnitude.length + 14) := by
  simpa only [delta_tapes, deltaLabels, resultTapes] using
    RationalFields.accepts computer.step deltaStacks deltaLabels delta_executes false
      (tapes outer.tape outer.problem e.denominator [] [] e.magnitude [e.negative] [] [])
      outer.delta d h

/-- This is one execution of the displayed finite machine, from the original
raw request through both rational checks. No prepared field is supplied by an
external callback. -/
theorem accepts (raw : List Bool) (outer : Contract.Fields) (e d : RationalFields.Fields)
    (ho : Contract.split raw = some outer)
    (he : RationalFields.separate outer.epsilon = some e)
    (hd : RationalFields.separate outer.delta = some d) :
    RunsExactly computer.step (initList computer raw)
      (cfg 18 false (resultTapes ⟨outer.problem, e, d, outer.tape⟩))
      (2 * (outer.problem.length + outer.epsilon.length + outer.delta.length) +
        2 * e.magnitude.length + 2 * d.magnitude.length + 34) := by
  have hr := ((outer_exact outer).trans (epsilon_accepts outer e he)).trans
    (delta_accepts outer e d hd)
  have ht : (2 * d.magnitude.length + 14) + ((2 * e.magnitude.length + 14) +
      (2 * (outer.problem.length + outer.epsilon.length + outer.delta.length) + 6)) =
      2 * (outer.problem.length + outer.epsilon.length + outer.delta.length) +
        2 * e.magnitude.length + 2 * d.magnitude.length + 34 := by omega
  rw [ht] at hr
  simpa only [Contract.split_some_raw ho] using hr


/-- The unchanged raw lengths, rather than the decoded numeric magnitudes,
control both rational parser invocations. -/
theorem rational_cost_le (raw : List Bool) (f : RationalFields.Fields)
    (h : RationalFields.separate raw = some f) :
    2 * f.magnitude.length + 14 ≤ 2 * raw.length + 8 := by
  rw [(RationalFields.separate_some h).1]
  simp only [RationalFields.join, List.length_append, Encoding.frame_length, List.length_singleton]
  omega

theorem field_reject (i : Fin 3) (frame : Stack → List Bool)
    (input output : List Bool) (h : Encoding.unframe input = none) :
    ∃ (produced : List Bool) (time : ℕ), time ≤ input.length + 1 ∧ produced.length ≤ input.length ∧
      RunsExactly computer.step
        (cfg (scanLabel i) false (tapes3 frame 0 (destination i) 4 input output []))
        (cfg 19 false (tapes3 frame 0 (destination i) 4 [] output produced.reverse)) time := by
  rw [Contract.unframe_eq] at h
  simpa only [List.append_nil] using Frame.rejects 0 (destination i) 4
    (by fin_cases i <;> decide) (by decide) computer.step
    (scanLabel i) (restoreLabel i) 19 (scan_executes i) false frame input output [] h

private theorem unframe_prefix {raw word rest : List Bool}
    (h : Encoding.unframe raw = some (word, rest)) :
    raw = Encoding.frame word ++ rest := by
  rw [Contract.unframe_eq] at h
  simpa only [Contract.frame_eq] using (Frame.unframe_some_iff raw word rest).mp h

/-- Every outer failure reaches this same program's failure continuation. -/
theorem outer_rejects (raw : List Bool) (h : Contract.split raw = none) :
    ∃ (saved : Stack → List Bool) (time : ℕ), time ≤ raw.length + 3 ∧
      RunsExactly computer.step (initList computer raw) (cfg 19 false saved) time := by
  cases hp : Encoding.unframe raw with
  | none =>
    obtain ⟨produced, time, ht, _, hr⟩ :=
      field_reject (0 : Fin 3) (tapes [] [] [] [] [] [] [] [] []) raw [] hp
    refine ⟨tapes [] [] [] [] produced.reverse [] [] [] [], time, by omega, ?_⟩
    simpa [scanLabel, destination, cfg_init] using hr
  | some p =>
    rcases p with ⟨p, rest⟩
    have hraw := unframe_prefix hp
    have hlen := congrArg List.length hraw
    simp only [List.length_append, Encoding.frame_length] at hlen
    cases he : Encoding.unframe rest with
    | none =>
      obtain ⟨produced, time, ht, _, hr⟩ :=
        field_reject (1 : Fin 3) (tapes [] p [] [] [] [] [] [] []) rest [] he
      have hf : RunsExactly computer.step (cfg 2 false (tapes rest p [] [] [] [] [] [] []))
          (cfg 19 false (tapes [] p [] [] produced.reverse [] [] [] [])) time := by
        simpa [scanLabel, destination] using hr
      have whole := (first_exact p rest [] []).trans hf
      refine ⟨tapes [] p [] [] produced.reverse [] [] [] [], time + 2 * (p.length + 1),
        by omega, ?_⟩
      simpa only [← hraw, cfg_init] using whole
    | some e =>
      rcases e with ⟨e, rest2⟩
      have hrest := unframe_prefix he
      have hlen2 := congrArg List.length hrest
      simp only [List.length_append, Encoding.frame_length] at hlen2
      cases hd : Encoding.unframe rest2 with
      | none =>
        obtain ⟨produced, time, ht, _, hr⟩ :=
          field_reject (2 : Fin 3) (tapes [] p e [] [] [] [] [] []) rest2 [] hd
        have hf : RunsExactly computer.step (cfg 4 false (tapes rest2 p e [] [] [] [] [] []))
            (cfg 19 false (tapes [] p e [] produced.reverse [] [] [] [])) time := by
          simpa [scanLabel, destination] using hr
        have first := first_exact p rest [] []
        rw [hrest] at first
        have whole := first.trans ((second_exact e rest2 p []).trans hf)
        refine ⟨tapes [] p e [] produced.reverse [] [] [] [],
          time + 2 * (e.length + 1) + 2 * (p.length + 1), by omega, ?_⟩
        simpa only [← hrest, ← hraw, cfg_init] using whole
      | some d => simp [Contract.split, hp, he, hd] at h

theorem epsilon_rejects (outer : Contract.Fields)
    (h : RationalFields.separate outer.epsilon = none) :
    ∃ (saved : Stack → List Bool) (time : ℕ), time ≤ 2 * outer.epsilon.length + 8 ∧
      RunsExactly computer.step
        (cfg 6 false (tapes outer.tape outer.problem outer.epsilon outer.delta [] [] [] [] []))
        (cfg 19 false saved) time := by
  obtain ⟨saved, time, ht, hr, _⟩ :=
    RationalFields.rejects computer.step epsilonStacks epsilonLabels epsilon_executes false
      (tapes outer.tape outer.problem [] outer.delta [] [] [] [] []) outer.epsilon h
  exact ⟨saved, time, ht, by simpa only [epsilon_tapes, epsilonLabels] using hr⟩

theorem delta_rejects (outer : Contract.Fields) (e : RationalFields.Fields)
    (h : RationalFields.separate outer.delta = none) :
    ∃ (saved : Stack → List Bool) (time : ℕ), time ≤ 2 * outer.delta.length + 8 ∧
      RunsExactly computer.step
        (cfg 12 false (tapes outer.tape outer.problem e.denominator outer.delta []
          e.magnitude [e.negative] [] []))
        (cfg 19 false saved) time := by
  obtain ⟨saved, time, ht, hr, _⟩ :=
    RationalFields.rejects computer.step deltaStacks deltaLabels delta_executes false
      (tapes outer.tape outer.problem e.denominator [] [] e.magnitude [e.negative] [] [])
      outer.delta h
  exact ⟨saved, time, ht, by simpa only [delta_tapes, deltaLabels] using hr⟩

/-- A connected all-input execution theorem. Malformed data may leave parser
residues, which the later request failure serializer must explicitly clear. -/
theorem allInputs (raw : List Bool) :
    ∃ (saved : Stack → List Bool) (time : ℕ), time ≤ 2 * raw.length + 19 ∧
      RunsExactly computer.step (initList computer raw)
        (cfg (if (separate raw).isSome then 18 else 19) false saved) time ∧
      ∀ f, separate raw = some f → saved = resultTapes f := by
  cases ho : Contract.split raw with
  | none =>
    obtain ⟨saved, time, ht, hr⟩ := outer_rejects raw ho
    have hs : separate raw = none := by simp [separate, ho]
    refine ⟨saved, time, by omega, ?_, ?_⟩
    · simpa only [hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using hr
    · intro f hf; rw [hs] at hf; cases hf
  | some outer =>
    have hl := Contract.split_length ho
    have r0 : RunsExactly computer.step (initList computer raw)
        (cfg 6 false (tapes outer.tape outer.problem outer.epsilon outer.delta [] [] [] [] []))
        (2 * (outer.problem.length + outer.epsilon.length + outer.delta.length) + 6) := by
      simpa only [Contract.split_some_raw ho] using outer_exact outer
    cases he : RationalFields.separate outer.epsilon with
    | none =>
      obtain ⟨saved, time, ht, hr⟩ := epsilon_rejects outer he
      have hs : separate raw = none := by simp [separate, ho, he]
      refine ⟨saved, time + (2 * (outer.problem.length + outer.epsilon.length +
        outer.delta.length) + 6), by omega, ?_, ?_⟩
      · simpa only [hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using r0.trans hr
      · intro f hf; rw [hs] at hf; cases hf
    | some e =>
      have rte := epsilon_accepts outer e he
      have hte := rational_cost_le outer.epsilon e he
      cases hd : RationalFields.separate outer.delta with
      | none =>
        obtain ⟨saved, time, ht, hr⟩ := delta_rejects outer e hd
        have hs : separate raw = none := by simp [separate, ho, he, hd]
        refine ⟨saved, time + ((2 * e.magnitude.length + 14) +
          (2 * (outer.problem.length + outer.epsilon.length + outer.delta.length) + 6)),
          by omega, ?_, ?_⟩
        · simpa only [hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using
            (r0.trans rte).trans hr
        · intro f hf; rw [hs] at hf; cases hf
      | some d =>
        have htd := rational_cost_le outer.delta d hd
        have hs : separate raw = some ⟨outer.problem, e, d, outer.tape⟩ := by
          simp [separate, ho, he, hd]
        refine ⟨resultTapes ⟨outer.problem, e, d, outer.tape⟩,
          2 * (outer.problem.length + outer.epsilon.length + outer.delta.length) +
            2 * e.magnitude.length + 2 * d.magnitude.length + 34, by omega, ?_, ?_⟩
        · simpa only [hs, Option.isSome_some, ↓reduceIte] using accepts raw outer e d ho he hd
        · intro f hf
          have hh : f = ⟨outer.problem, e, d, outer.tape⟩ := Option.some.inj (hf.symm.trans hs)
          subst f
          rfl

theorem return_halts (good : Bool) (saved : Stack → List Bool) :
    computer.step (cfg (if good then 18 else 19) false saved) =
      some (⟨none, (none, good), saved⟩ : Config) := by
  cases good <;> rfl

/-- Actual halting of the connected finite parser, including every malformed
input. The output is the exposed stack layout, not yet R1's serialized result. -/
theorem terminates (raw : List Bool) :
    ∃ (saved : Stack → List Bool) (time : ℕ), time ≤ 2 * raw.length + 20 ∧
      RunsExactly computer.step (initList computer raw)
        (⟨none, (none, (separate raw).isSome), saved⟩ : Config) time := by
  obtain ⟨saved, time, ht, hr, _⟩ := allInputs raw
  refine ⟨saved, 1 + time, by omega, ?_⟩
  exact hr.trans (runsExactly_one (return_halts (separate raw).isSome saved))

end Counting.Algorithm.KarpLubyRequest.Preamble
