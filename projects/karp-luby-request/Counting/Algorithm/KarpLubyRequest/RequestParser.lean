import Counting.Algorithm.KarpLubyRequest.DNFVerifier
import Counting.Algorithm.KarpLubyRequest.Embedded
import Counting.Algorithm.KarpLubyRequest.ProblemHeader

/-!
# The complete raw request decoder as one finite program

The first block is the complete preamble and variable-header machine. Its
materialized formula and variable word are physically copied into the nested
DNF verifier; all original fields and the fair-bit tape remain in the caller's
bank. Both copies, dispatches, and the final halt belong to the same run.
-/
namespace Counting.Algorithm.KarpLubyRequest.RequestParser
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby

abbrev Stack := ProblemHeader.Stack ⊕ (DNFVerifier.Stack ⊕ Fin 1)
abbrev Label := ProblemHeader.Label ⊕ (DNFVerifier.Label ⊕ Fin 8)
abbrev Config := Cfg Stack Label Bool

def headerMap : ProblemHeader.Stack ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩
def formulaMap : DNFVerifier.Stack ↪ Stack :=
  ⟨fun k => .inr (.inl k), fun _ _ h => Sum.inl_injective (Sum.inr_injective h)⟩
@[simp] theorem headerMap_apply (k : ProblemHeader.Stack) : headerMap k = Sum.inl k := rfl
@[simp] theorem formulaMap_apply (k : DNFVerifier.Stack) : formulaMap k = Sum.inr (Sum.inl k) := rfl
def headerLabel (l : ProblemHeader.Label) : Label := .inl l
def formulaLabel (l : DNFVerifier.Label) : Label := .inr (.inl l)
def own (l : Fin 8) : Label := .inr (.inr l)
def scratch : Stack := .inr (.inr 0)
def formulaSource : Stack := headerMap ProblemHeader.source
def variableSource : Stack := headerMap ProblemHeader.destination
def formulaInput : Stack := formulaMap DNFVerifier.formula.input
def formulaAmbient : Stack := formulaMap DNFVerifier.formula.ambient

def outside (l : Fin 8) : Stmt Stack Label Bool :=
  if l = 0 then .branch (fun s => s.2) (.goto (fun _ => own 1)) (.goto (fun _ => own 7))
  else if l = 1 then copyMoveStmt formulaSource scratch (own 1) (own 2)
  else if l = 2 then copyRestoreStmt formulaSource formulaInput scratch (own 2) (own 3)
  else if l = 3 then copyMoveStmt variableSource scratch (own 3) (own 4)
  else if l = 4 then copyRestoreStmt variableSource formulaAmbient scratch (own 4) (own 5)
  else if l = 5 then .load (fun _ => (none, false)) (.goto (fun _ => formulaLabel DNFVerifier.computer.main))
  else if l = 6 then .halt
  else .load (fun _ => (none, false)) .halt

def program : Label → Stmt Stack Label Bool
  | .inl l => Embedded.block headerMap headerLabel (own 0) (ProblemHeader.computer.m l)
  | .inr (.inl l) => Embedded.block formulaMap formulaLabel (own 6) (DNFVerifier.computer.m l)
  | .inr (.inr l) => outside l

abbrev computer : FinTM2 where
  K := Stack
  k₀ := headerMap ProblemHeader.computer.k₀
  k₁ := headerMap ProblemHeader.computer.k₁
  Γ _ := Bool
  Λ := Label
  main := headerLabel ProblemHeader.computer.main
  σ := Option Bool × Bool
  initialState := (none, false)
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) :=
  inferInstanceAs (Fintype Bool)

def bank (header : ProblemHeader.Stack → List Bool)
    (source : DNFVerifier.Stack → List Bool) (temporary : List Bool) : Stack → List Bool :=
  Sum.elim header (Sum.elim source (fun _ => temporary))

def tapes (header : ProblemHeader.Stack → List Bool) (raw original : List Bool) : Stack → List Bool :=
  bank header (verifierTapes DNFVerifier.formula.input DNFVerifier.formula.ambient raw original) []

@[simp] theorem tapes_header (header : ProblemHeader.Stack → List Bool) (raw original : List Bool)
    (k : ProblemHeader.Stack) : tapes header raw original (headerMap k) = header k := rfl
@[simp] theorem tapes_input (header : ProblemHeader.Stack → List Bool) (raw original : List Bool) :
    tapes header raw original formulaInput = raw := rfl
@[simp] theorem tapes_ambient (header : ProblemHeader.Stack → List Bool) (raw original : List Bool) :
    tapes header raw original formulaAmbient = original := rfl
@[simp] theorem tapes_scratch (header : ProblemHeader.Stack → List Bool) (raw original : List Bool) :
    tapes header raw original scratch = [] := rfl

theorem statement_budget (label : Label) : TM2Cost.budget (program label) ≤ 10 := by
  cases label with
  | inl l =>
    simpa only [program, Embedded.statement_budget] using ProblemHeader.statement_budget l
  | inr l =>
    cases l with
    | inl l => simpa only [program, Embedded.statement_budget] using DNFVerifier.statement_budget l
    | inr l =>
      fin_cases l <;> simp [program, outside, copyMoveStmt, copyRestoreStmt, TM2Cost.budget]

private theorem initial_rel (raw : List Bool) :
    Embedded.Rel headerMap headerLabel (own 0) (fun _ => [])
      (initList ProblemHeader.computer raw) (initList computer raw) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro k
    cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  · intro j hj
    cases j with
    | inl k => exact False.elim (hj k rfl)
    | inr k => rfl

/-- The entire already verified header machine is an actual first block. -/
theorem header_run (raw : List Bool) (ending : ProblemHeader.Stack → List Bool) (time : ℕ)
    (hr : RunsExactly ProblemHeader.computer.step (initList ProblemHeader.computer raw)
      (⟨none, (none, (ProblemHeader.separate raw).isSome), ending⟩ : ProblemHeader.Config) time) :
    RunsExactly computer.step (initList computer raw)
      (cfg (own 0) (ProblemHeader.separate raw).isSome (tapes ending [] [])) time := by
  obtain ⟨last, hl, hrel⟩ := Embedded.run headerMap headerLabel (own 0)
    ProblemHeader.computer.m program (by intro l; rfl) _ _ (initList computer raw)
    (fun _ => []) time (initial_rel raw) hr
  have ht : last.stk = tapes ending [] [] := by
    funext k
    cases k with
    | inl k => exact hrel.2.2.1 k
    | inr k =>
      have hh := hrel.2.2.2 (.inr k) (fun j => by simp [headerMap_apply])
      cases k with
      | inl k => simpa [tapes, bank, verifierTapes] using hh
      | inr k => exact hh
  have he : last = cfg (own 0) (ProblemHeader.separate raw).isSome (tapes ending [] []) := by
    cases last
    simp only [Embedded.Rel, Option.elim_none] at hrel
    simp_all [cfg]
  change RunsExactly computer.step _ _ time at hl
  simpa only [he] using hl

private theorem update_input (header : ProblemHeader.Stack → List Bool) (raw original : List Bool) :
    Function.update (tapes header [] original) formulaInput raw = tapes header raw original := by
  have hne := DNFVerifier.formula.distinct
  funext k
  simp only [tapes, bank, verifierTapes, formulaInput, formulaMap_apply, Function.update_apply]
  cases k with
  | inl k => simp
  | inr k =>
    cases k with
    | inr k => simp
    | inl k =>
      by_cases hi : k = DNFVerifier.formula.input <;>
        by_cases ha : k = DNFVerifier.formula.ambient <;> simp_all

private theorem update_ambient (header : ProblemHeader.Stack → List Bool) (raw original : List Bool) :
    Function.update (tapes header raw []) formulaAmbient original = tapes header raw original := by
  funext k
  simp only [tapes, bank, verifierTapes, formulaAmbient, formulaMap_apply, Function.update_apply]
  cases k with
  | inl k => simp
  | inr k =>
    cases k with
    | inr k => simp
    | inl k => by_cases ha : k = DNFVerifier.formula.ambient <;> simp_all

/-- Both input fields are copied by real two-pass stack code. The caller's
formula and variable stacks, ε/δ fields and random tape are retained. -/
theorem copy_fields (header : ProblemHeader.Stack → List Bool) :
    RunsExactly computer.step (cfg (own 1) true (tapes header [] []))
      (cfg (formulaLabel DNFVerifier.computer.main) false
        (tapes header (header ProblemHeader.source) (header ProblemHeader.destination)))
      (1 + ((2 * (header ProblemHeader.destination).length + 2) +
        (2 * (header ProblemHeader.source).length + 2))) := by
  have firstRun := Embedded.copy_into formulaSource formulaInput scratch
    (by simp [formulaSource, formulaInput, headerMap_apply, formulaMap_apply])
    (by simp [formulaSource, headerMap_apply, scratch])
    (by simp [formulaInput, formulaMap_apply, scratch])
    computer.step (own 1) (own 2) (own 3)
    (by intro state stk; rfl) (by intro state stk; rfl) true (tapes header [] []) (by rfl) (by rfl)
  simp only [formulaSource, tapes_header, update_input] at firstRun
  have secondRun := Embedded.copy_into variableSource formulaAmbient scratch
    (by simp [variableSource, formulaAmbient, headerMap_apply, formulaMap_apply])
    (by simp [variableSource, headerMap_apply, scratch])
    (by simp [formulaAmbient, formulaMap_apply, scratch])
    computer.step (own 3) (own 4) (own 5)
    (by intro state stk; rfl) (by intro state stk; rfl) true
    (tapes header (header ProblemHeader.source) []) (by rfl) (by rfl)
  simp only [variableSource, tapes_header, update_ambient] at secondRun
  exact (firstRun.trans secondRun).trans (runsExactly_one (show computer.step
    (cfg (own 5) true (tapes header (header ProblemHeader.source) (header ProblemHeader.destination))) =
    some (cfg (formulaLabel DNFVerifier.computer.main) false
      (tapes header (header ProblemHeader.source) (header ProblemHeader.destination))) from rfl))

/-- The nested verifier runs in the shared bank without changing any header
field, and returns the original formula codec's exact success bit. -/
theorem formula_run (header : ProblemHeader.Stack → List Bool) (raw original : List Bool) :
    ∃ ending time, time ≤ DNFVerifier.timeBound raw.length original.length ∧
      RunsExactly computer.step
        (cfg (formulaLabel DNFVerifier.computer.main) false (tapes header raw original))
        (cfg (own 6) ((Encoding.formula original.length).decode raw).isSome ending) time ∧
      (∀ k, ending (headerMap k) = header k) ∧
      (((Encoding.formula original.length).decode raw).isSome = true →
        ending = tapes header [] original) := by
  obtain ⟨saved, time, ht, hr, hs⟩ := DNFVerifier.run raw original
  have hi : Embedded.Rel formulaMap formulaLabel (own 6) (tapes header raw original)
      (cfg DNFVerifier.computer.main false
        (verifierTapes DNFVerifier.formula.input DNFVerifier.formula.ambient raw original))
      (cfg (formulaLabel DNFVerifier.computer.main) false (tapes header raw original)) := by
    exact ⟨rfl, rfl, fun _ => rfl, fun _ _ => rfl⟩
  obtain ⟨last, hl, hrel⟩ := Embedded.run formulaMap formulaLabel (own 6)
    DNFVerifier.computer.m program (by intro l; rfl) _ _ _ _ time hi hr
  have he : last = cfg (own 6) ((Encoding.formula original.length).decode raw).isSome last.stk := by
    cases last
    simp only [Embedded.Rel, Option.elim_none] at hrel
    rcases hrel with ⟨hl, hv, _⟩
    simp only [cfg] at *
    congr
  refine ⟨last.stk, time, ht, ?_, ?_, ?_⟩
  · rw [he] at hl
    exact hl
  · intro k
    exact hrel.2.2.2 (headerMap k) (fun j => by simp [headerMap_apply, formulaMap_apply])
  · intro good
    have htape := hs good
    funext k
    cases k with
    | inl k => exact hrel.2.2.2 (headerMap k) (fun j => by simp [headerMap_apply, formulaMap_apply])
    | inr k =>
      cases k with
      | inl k => simpa only [htape, formulaMap_apply, tapes, bank, Sum.elim_inr, Sum.elim_inl] using hrel.2.2.1 k
      | inr k => exact hrel.2.2.2 (.inr (.inr k)) (fun j => by simp [formulaMap_apply])

/-- Exact caller fields after parsing; the original rational raw components and
fair-bit tape remain available for subsequent arithmetic and sampling stages. -/
def outputTapes (f : ProblemHeader.Fields) : ProblemHeader.Stack → List Bool :=
  ProblemHeader.resultTapes
    ⟨Encoding.frame f.variableWord ++ f.formula, f.epsilon, f.delta, f.tape⟩
    f.variableWord f.formula

private theorem result_eq (p : Preamble.Fields) (word body : List Bool) :
    ProblemHeader.resultTapes p word body = outputTapes ⟨word, body, p.epsilon, p.delta, p.tape⟩ := by
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

@[simp] theorem output_source (f : ProblemHeader.Fields) : outputTapes f ProblemHeader.source = f.formula := rfl
@[simp] theorem output_variables (f : ProblemHeader.Fields) :
    outputTapes f ProblemHeader.destination = f.variableWord := rfl

/-- Complete source-prefix refinement, retaining the exact materialized fields
on the success branch. Malformed raw prefixes require no validity premise. -/
theorem prefix_run (raw : List Bool) :
    ∃ header time, time ≤ 3 * raw.length + 24 ∧
      RunsExactly computer.step (initList computer raw)
        (cfg (own 0) (ProblemHeader.separate raw).isSome (tapes header [] [])) time ∧
      (∀ f, ProblemHeader.separate raw = some f → header = outputTapes f) := by
  cases hs : ProblemHeader.separate raw with
  | none =>
    obtain ⟨header, time, ht, hr⟩ := ProblemHeader.terminates raw
    exact ⟨header, time, ht, by simpa only [hs] using header_run raw header time hr, by simp⟩
  | some f =>
    cases hp : Preamble.separate raw with
    | none => simp [ProblemHeader.separate, hp] at hs
    | some p =>
      cases hu : Encoding.unframe p.problem with
      | none => simp [ProblemHeader.separate, hp, hu] at hs
      | some pair =>
        rcases pair with ⟨word, body⟩
        simp [ProblemHeader.separate, hp, hu] at hs
        subst f
        obtain ⟨time, ht, hr⟩ := ProblemHeader.accepts raw p word body hp hu
        have final := hr.trans (runsExactly_one (ProblemHeader.success_halts
          (ProblemHeader.resultTapes p word body)))
        have hf : ProblemHeader.separate raw = some ⟨word, body, p.epsilon, p.delta, p.tape⟩ := by
          simp [ProblemHeader.separate, hp, hu]
        have final' : RunsExactly ProblemHeader.computer.step (initList ProblemHeader.computer raw)
            (⟨none, (none, (ProblemHeader.separate raw).isSome), ProblemHeader.resultTapes p word body⟩ :
              ProblemHeader.Config) (1 + time) := by simpa only [hf, Option.isSome_some] using final
        refine ⟨ProblemHeader.resultTapes p word body, 1 + time, ?_,
          by simpa only [hf] using header_run raw _ _ final', ?_⟩
        · have hpLen := ProblemHeader.problem_length_le raw p hp
          have he := congrArg List.length (NestedSemantics.unframe_raw hu)
          simp only [List.length_append, Encoding.frame_length] at he
          omega
        · intro f h
          have hh := Option.some.inj h
          subst f
          exact result_eq p word body

/-- Both physically copied fields fit the original encoded request, even when
the formula decoder subsequently rejects the field. -/
theorem field_lengths {raw : List Bool} {f : ProblemHeader.Fields}
    (h : ProblemHeader.separate raw = some f) :
    f.formula.length ≤ raw.length ∧ f.variableWord.length ≤ raw.length := by
  cases hp : Preamble.separate raw with
  | none => simp [ProblemHeader.separate, hp] at h
  | some p =>
    cases hu : Encoding.unframe p.problem with
    | none => simp [ProblemHeader.separate, hp, hu] at h
    | some pair =>
      rcases pair with ⟨word, body⟩
      simp [ProblemHeader.separate, hp, hu] at h
      subst f
      have hpLen := ProblemHeader.problem_length_le raw p hp
      have he := congrArg List.length (NestedSemantics.unframe_raw hu)
      simp only [List.length_append, Encoding.frame_length] at he
      constructor <;> dsimp <;> omega

private theorem status_none {raw : List Bool} (h : ProblemHeader.separate raw = none) :
    (ProgramEncoding.request.decode raw).isSome = false := by
  rw [← ProblemHeader.decode_eq, h]
  rfl

private theorem status_some {raw : List Bool} {f : ProblemHeader.Fields}
    (h : ProblemHeader.separate raw = some f) :
    (ProgramEncoding.request.decode raw).isSome = ((Encoding.formula f.variableWord.length).decode f.formula).isSome := by
  rw [← ProblemHeader.decode_eq, h]
  simp only [Option.bind_some, ProblemHeader.validate]
  cases (Encoding.formula f.variableWord.length).decode f.formula <;> rfl

/-- Physical-input polynomial for the entire raw decoder, including both copied
fields and the complete nested DNF program. -/
def timeBound (n : ℕ) := DNFVerifier.timeBound n n + 7 * n + 31

theorem timeBound_eq (n : ℕ) :
    timeBound n = 2 * n ^ 4 + 18 * n ^ 3 + 39 * n ^ 2 + 44 * n + 50 := by
  unfold timeBound DNFVerifier.timeBound
  ring

/-- One fixed finite TM2 decides the unchanged raw request decoder on every bit
string. Successful runs preserve every materialized caller field for the next
execution stages. This is a parser theorem, not an estimator/FPRAS theorem. -/
theorem terminates (raw : List Bool) :
    ∃ ending time, time ≤ timeBound raw.length ∧
      RunsExactly computer.step (initList computer raw)
        (⟨none, (none, (ProgramEncoding.request.decode raw).isSome), ending⟩ : computer.Cfg) time ∧
      (∀ f, ProblemHeader.separate raw = some f →
        ∀ k, ending (headerMap k) = outputTapes f k) := by
  obtain ⟨header, first, ht, hr, hh⟩ := prefix_run raw
  cases hs : ProblemHeader.separate raw with
  | none =>
    have h1 := runsExactly_one (show computer.step (cfg (own 0) false (tapes header [] [])) =
      some (cfg (own 7) false (tapes header [] [])) from rfl)
    have h2 := runsExactly_one (show computer.step (cfg (own 7) false (tapes header [] [])) =
      some (⟨none, (none, false), tapes header [] []⟩ : computer.Cfg) from rfl)
    simp only [hs, Option.isSome_none] at hr
    refine ⟨tapes header [] [], 1 + (1 + first), by unfold timeBound; omega, ?_, by simp [hs]⟩
    simpa only [status_none hs] using (hr.trans h1).trans h2
  | some f =>
    have he := hh f hs
    subst header
    simp only [hs, Option.isSome_some] at hr
    have h1 := runsExactly_one (show computer.step (cfg (own 0) true (tapes (outputTapes f) [] [])) =
      some (cfg (own 1) true (tapes (outputTapes f) [] [])) from rfl)
    have h2 := copy_fields (outputTapes f)
    simp only [output_source, output_variables] at h2
    obtain ⟨ending, more, hm, h3, keep, _⟩ := formula_run (outputTapes f) f.formula f.variableWord
    have h4 := runsExactly_one (show computer.step
      (cfg (own 6) ((Encoding.formula f.variableWord.length).decode f.formula).isSome ending) =
      some (⟨none, (none, ((Encoding.formula f.variableWord.length).decode f.formula).isSome), ending⟩ : computer.Cfg)
      from rfl)
    refine ⟨ending, 1 + (more + ((1 + ((2 * f.variableWord.length + 2) +
      (2 * f.formula.length + 2))) + (1 + first))), ?_, ?_, ?_⟩
    · obtain ⟨hf, hv⟩ := field_lengths hs
      have hb := DNFVerifier.formula.monotone hf hv
      rw [DNFVerifier.bound_eq, DNFVerifier.bound_eq] at hb
      unfold timeBound
      omega
    · simpa only [status_some hs] using (((hr.trans h1).trans h2).trans h3).trans h4
    · intro g hg k
      have he := Option.some.inj hg
      subst g
      exact keep k

/-- Actual interpreter bit cost for this same full legal/illegal decoder run. -/
theorem bit_cost (raw : List Bool) :
    ∃ ending time, time ≤ timeBound raw.length ∧
      (Primitive.run program time (some (initList computer raw))).2 =
        some (⟨none, (none, (ProgramEncoding.request.decode raw).isSome), ending⟩ : computer.Cfg) ∧
      (Primitive.run program time (some (initList computer raw))).1 ≤ 10 * timeBound raw.length := by
  obtain ⟨ending, time, ht, hr, _⟩ := terminates raw
  have hc := Primitive.execution_cost program 10 statement_budget time _ _ hr
  exact ⟨ending, time, ht, hc.1, hc.2.trans (Nat.mul_le_mul_left 10 ht)⟩

end Counting.Algorithm.KarpLubyRequest.RequestParser
