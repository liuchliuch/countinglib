import Counting.Algorithm.KarpLubyRequest.Contract
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-!
# Returning raw rational-field validation on Boolean stacks

The unchanged R1 decoder first unframes an integer word, then unframes its
single sign bit. The remaining two raw words are retained verbatim. In the
locked mathlib codec, `Computability.decodeNat [] = 0` and every nonempty word decodes to a
positive number: notably `[false]` decodes to two, not zero. The denominator
test below is justified by that exact codec theorem, rather than by a different
little-endian fold convention.

H1's actual returning frame parser is reused without copying its provider.
The new statements validate a singleton and peek/restore one denominator bit.
They use only `Option Bool × τ` control, retain arbitrary caller memory, and
preserve every unselected stack. Success leaves denominator, raw magnitude (or
negative predecessor), and singleton sign on three separate stacks. Failure
returns with explicitly described parser residues; caller cleanup is separate.
Neither natural decoding nor `mkRat` is an opcode, and normalization is not
claimed here.
-/

namespace Counting.Algorithm.KarpLubyRequest.RationalFields

open Turing Computability
open Turing.TM2.Stmt
open Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby

/-- This property concerns the actual locked decoder on all raw words. -/
theorem decodeNat_eq_zero_iff (word : List Bool) : Computability.decodeNat word = 0 ↔ word = [] := by
  dsimp only [Computability.decodeNat, decodeNum]
  by_cases h : word = []
  · subst word; simp
  · have hp := PosNum.to_nat_pos (decodePosNum word)
    simp only [ite_eq_right h, PosNum.cast_to_num, Num.cast_pos]
    exact iff_of_false (Nat.ne_of_gt hp) h

theorem bool_decode (raw : List Bool) : Encoding.bool.decode raw =
    (match raw with | [b] => some b | _ => none) := rfl

structure Fields where
  negative : Bool
  magnitude : List Bool
  denominator : List Bool
  deriving DecidableEq

/-- Semantic interpretation only; no unbounded number is held in control. -/
def value (f : Fields) : ℚ :=
  mkRat (if f.negative then Int.negSucc (Computability.decodeNat f.magnitude)
    else Int.ofNat (Computability.decodeNat f.magnitude)) (Computability.decodeNat f.denominator)

/-- Retain raw component words while applying precisely R1's validity tests. -/
def separate (raw : List Bool) : Option Fields := do
  let (integer, denominator) ← Encoding.unframe raw
  let (sign, magnitude) ← Encoding.unframe integer
  let negative ← Encoding.bool.decode sign
  if denominator = [] then none else some ⟨negative, magnitude, denominator⟩

def join (f : Fields) : List Bool :=
  Encoding.frame (Encoding.frame [f.negative] ++ f.magnitude) ++ f.denominator

@[simp] theorem separate_join (f : Fields) (h : f.denominator ≠ []) :
    separate (join f) = some f := by
  cases f
  simp_all [separate, join, bool_decode]

/-- The bitfield validator has exactly the original rational decoder's result,
including noncanonical natural words and negative predecessor coding. -/
theorem output_decode_eq (raw : List Bool) :
    Encoding.output.decode raw = (separate raw).map value := by
  dsimp only [Encoding.output, Encoding.int, Encoding.retract]
  cases ho : Encoding.unframe raw with
  | none => simp [Encoding.output, Encoding.prod, separate, ho]
  | some p =>
    rcases p with ⟨integer, denominator⟩
    cases hi : Encoding.unframe integer with
    | none => simp [Encoding.output, Encoding.prod, separate, ho, hi]
    | some p =>
      rcases p with ⟨sign, magnitude⟩
      cases sign with
      | nil => simp [Encoding.output, Encoding.prod, 
          bool_decode, separate, ho, hi]
      | cons b rest =>
        cases rest with
        | nil =>
          by_cases hd : denominator = [] <;>
            simp [Encoding.output, Encoding.prod, 
              bool_decode, Encoding.nat, separate, value, ho, hi, decodeNat_eq_zero_iff, hd]
        | cons c rest =>
          simp [Encoding.output, Encoding.prod, 
            bool_decode, separate, ho, hi]

theorem separate_some {raw : List Bool} {f : Fields} (h : separate raw = some f) :
    raw = join f ∧ f.denominator ≠ [] := by
  unfold separate at h
  cases ho : Encoding.unframe raw with
  | none => simp [ho] at h
  | some p =>
    rcases p with ⟨integer, denominator⟩
    cases hi : Encoding.unframe integer with
    | none => simp [ho, hi] at h
    | some p =>
      rcases p with ⟨sign, magnitude⟩
      cases sign with
      | nil => simp [ho, hi, bool_decode] at h
      | cons b rest =>
        cases rest with
        | cons c rest => simp [ho, hi, bool_decode] at h
        | nil =>
          by_cases hd : denominator = []
          · simp [ho, hi, bool_decode, hd] at h
          · simp [ho, hi, bool_decode, hd] at h
            subst f
            rw [Contract.unframe_eq] at ho hi
            refine ⟨?_, hd⟩
            rw [(GraphPreprocessing.Frame.unframe_some_iff _ _ _).mp ho,
              (GraphPreprocessing.Frame.unframe_some_iff _ _ _).mp hi]
            simp only [join, Contract.frame_eq]

variable {K Λ τ : Type} [DecidableEq K]

/-- Stack positions: denominator/source, magnitude/integer, sign, scratch. -/
abbrev Stacks (K : Type) := Fin 4 ↪ K

structure Labels (Λ : Type) where
  outerScan : Λ
  outerRestore : Λ
  signScan : Λ
  signRestore : Λ
  checkSign : Λ
  checkDenominator : Λ
  good : Λ
  bad : Λ

private def singletonTailStmt (stack : K) (first : Bool) (good bad : Λ) : Stmt K Λ τ :=
  pop stack (fun v bit => (bit, v.2))
    (branch (fun v => v.1.isSome)
      (push stack (fun v => v.1.getD false)
        (push stack (fun _ => first)
          (load (fun v => (none, v.2)) (goto (fun _ => bad)))))
      (push stack (fun _ => first)
        (load (fun v => (none, v.2)) (goto (fun _ => good)))))

/-- Inspect at most two symbols and restore both, accepting exactly one bit. -/
def singletonStmt (stack : K) (good bad : Λ) : Stmt K Λ τ :=
  pop stack (fun v bit => (bit, v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (singletonTailStmt stack true good bad)
        (singletonTailStmt stack false good bad))
      (load (fun v => (none, v.2)) (goto (fun _ => bad))))

/-- For this exact `Computability.decodeNat`, peeking one symbol is a complete nonzero test. -/
def denominatorStmt (stack : K) (good bad : Λ) : Stmt K Λ τ :=
  pop stack (fun v bit => (bit, v.2))
    (branch (fun v => v.1.isSome)
      (push stack (fun v => v.1.getD false)
        (load (fun v => (none, v.2)) (goto (fun _ => good))))
      (load (fun v => (none, v.2)) (goto (fun _ => bad))))

/-- Only equations for the six displayed statements are required of a caller. -/
structure Executes (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (st : Stacks K) (lab : Labels Λ) : Prop where
  outerScan : ExecutesAt step lab.outerScan
    (GraphPreprocessing.Frame.scanStmt (st 0) (st 3) lab.outerScan lab.outerRestore lab.bad)
  outerRestore : ExecutesAt step lab.outerRestore
    (copyMoveStmt (st 3) (st 1) lab.outerRestore lab.signScan)
  signScan : ExecutesAt step lab.signScan
    (GraphPreprocessing.Frame.scanStmt (st 1) (st 3) lab.signScan lab.signRestore lab.bad)
  signRestore : ExecutesAt step lab.signRestore
    (copyMoveStmt (st 3) (st 2) lab.signRestore lab.checkSign)
  checkSign : ExecutesAt step lab.checkSign (singletonStmt (st 2) lab.checkDenominator lab.bad)
  checkDenominator : ExecutesAt step lab.checkDenominator (denominatorStmt (st 0) lab.good lab.bad)

def tapes (st : Stacks K) (frame : K → List Bool)
    (source magnitude sign scratch : List Bool) : K → List Bool :=
  tapes3 (Function.update frame (st 2) sign) (st 0) (st 1) (st 3) source magnitude scratch

@[simp] theorem tapes_at (st : Stacks K) (frame : K → List Bool)
    (source magnitude sign scratch : List Bool) (i : Fin 4) :
    tapes st frame source magnitude sign scratch (st i) =
      (![source, magnitude, sign, scratch] : Fin 4 → List Bool) i := by
  fin_cases i <;> simp [tapes, tapes3, st.injective.eq_iff]

theorem tapes_other (st : Stacks K) (frame : K → List Bool)
    (source magnitude sign scratch : List Bool) (k : K)
    (h : ∀ i : Fin 4, k ≠ st i) : tapes st frame source magnitude sign scratch k = frame k := by
  simp [tapes, tapes3, h]

private theorem tapes_inner (st : Stacks K) (frame : K → List Bool)
    (source magnitude sign scratch : List Bool) :
    tapes st frame source magnitude sign scratch =
      tapes3 (Function.update frame (st 0) source) (st 1) (st 2) (st 3) magnitude sign scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    simp_all [tapes, tapes3, st.injective.eq_iff]

private theorem update_tapes_same (st : Stacks K) (frame : K → List Bool)
    (source magnitude sign scratch : List Bool) (i : Fin 4) :
    Function.update (tapes st frame source magnitude sign scratch) (st i)
      ((![source, magnitude, sign, scratch] : Fin 4 → List Bool) i) =
      tapes st frame source magnitude sign scratch := by
  rw [← tapes_at st frame source magnitude sign scratch i]
  exact Function.update_eq_self _ _

theorem singleton_step (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (stack : K) (check good bad : Λ)
    (h : ExecutesAt step check (singletonStmt stack good bad))
    (memory : τ) (frame : K → List Bool) (word : List Bool) :
    step (cfg check memory (Function.update frame stack word)) =
      some (cfg (if word.length = 1 then good else bad) memory (Function.update frame stack word)) := by
  rw [cfg, h]
  cases word with
  | nil => simp [singletonStmt, singletonTailStmt, TM2.stepAux, cfg, Function.update_idem]
  | cons b rest =>
    cases b <;> cases rest <;>
      simp [singletonStmt, singletonTailStmt, TM2.stepAux, cfg, Function.update_idem]

theorem denominator_step (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (stack : K) (check good bad : Λ)
    (h : ExecutesAt step check (denominatorStmt stack good bad))
    (memory : τ) (frame : K → List Bool) (word : List Bool) :
    step (cfg check memory (Function.update frame stack word)) =
      some (cfg (if word = [] then bad else good) memory (Function.update frame stack word)) := by
  rw [cfg, h]
  cases word <;> simp [denominatorStmt, TM2.stepAux, cfg, Function.update_idem]

section Returning

variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (st : Stacks K) (lab : Labels Λ)
variable (exec : Executes step st lab) (memory : τ) (frame : K → List Bool)

omit [DecidableEq K] in
private theorem neq (i j : Fin 4) (h : i ≠ j) : st i ≠ st j := fun e => h (st.injective e)

include exec

theorem outer_exact (integer denominator : List Bool) :
    RunsExactly step
      (cfg lab.outerScan memory (tapes st frame (Encoding.frame integer ++ denominator) [] [] []))
      (cfg lab.signScan memory (tapes st frame denominator integer [] []))
      (2 * (integer.length + 1)) := by
  simpa only [tapes, Contract.frame_eq, List.append_nil] using
    GraphPreprocessing.Frame.extract_exact (st 0) (st 1) (st 3)
      (neq st 0 1 (by decide)) (neq st 0 3 (by decide)) (neq st 1 3 (by decide))
      step lab.outerScan lab.outerRestore lab.signScan lab.bad exec.outerScan exec.outerRestore
      memory (Function.update frame (st 2) []) integer denominator []

theorem inner_exact (sign magnitude denominator : List Bool) :
    RunsExactly step
      (cfg lab.signScan memory (tapes st frame denominator (Encoding.frame sign ++ magnitude) [] []))
      (cfg lab.checkSign memory (tapes st frame denominator magnitude sign []))
      (2 * (sign.length + 1)) := by
  simpa only [tapes_inner, Contract.frame_eq, List.append_nil] using
    GraphPreprocessing.Frame.extract_exact (st 1) (st 2) (st 3)
      (neq st 1 2 (by decide)) (neq st 1 3 (by decide)) (neq st 2 3 (by decide))
      step lab.signScan lab.signRestore lab.checkSign lab.bad exec.signScan exec.signRestore
      memory (Function.update frame (st 0) denominator) sign magnitude []

theorem sign_step (sign magnitude denominator : List Bool) :
    step (cfg lab.checkSign memory (tapes st frame denominator magnitude sign [])) =
      some (cfg (if sign.length = 1 then lab.checkDenominator else lab.bad)
        memory (tapes st frame denominator magnitude sign [])) := by
  have he : Function.update (tapes st frame denominator magnitude sign []) (st 2) sign =
      tapes st frame denominator magnitude sign [] :=
    update_tapes_same st frame denominator magnitude sign [] 2
  simpa only [he] using singleton_step step (st 2)
    lab.checkSign lab.checkDenominator lab.bad exec.checkSign memory
    (tapes st frame denominator magnitude sign []) sign

theorem den_step (sign magnitude denominator : List Bool) :
    step (cfg lab.checkDenominator memory (tapes st frame denominator magnitude sign [])) =
      some (cfg (if denominator = [] then lab.bad else lab.good)
        memory (tapes st frame denominator magnitude sign [])) := by
  have he : Function.update (tapes st frame denominator magnitude sign []) (st 0) denominator =
      tapes st frame denominator magnitude sign [] :=
    update_tapes_same st frame denominator magnitude sign [] 0
  simpa only [he] using denominator_step step (st 0)
    lab.checkDenominator lab.good lab.bad exec.checkDenominator memory
    (tapes st frame denominator magnitude sign []) denominator

/-- A successful call preserves both raw words, sign, caller memory and frame. -/
theorem accepts_exact (f : Fields) (hd : f.denominator ≠ []) :
    RunsExactly step
      (cfg lab.outerScan memory (tapes st frame (join f) [] [] []))
      (cfg lab.good memory (tapes st frame f.denominator f.magnitude [f.negative] []))
      (2 * f.magnitude.length + 14) := by
  have r1 := outer_exact step st lab exec memory frame
    (Encoding.frame [f.negative] ++ f.magnitude) f.denominator
  have r2 := inner_exact step st lab exec memory frame [f.negative] f.magnitude f.denominator
  have r3 := runsExactly_one (sign_step step st lab exec memory frame
    [f.negative] f.magnitude f.denominator)
  have r4 := runsExactly_one (den_step step st lab exec memory frame
    [f.negative] f.magnitude f.denominator)
  simp only [List.length_singleton, ↓reduceIte] at r3
  simp only [ite_eq_right hd] at r4
  have run := ((r1.trans r2).trans r3).trans r4
  convert run using 1
  · rfl
  · simp only [Encoding.frame_length, List.length_append, List.length_singleton]; omega

/-- The accepted grammar is exactly the existing rational decoder grammar. -/
theorem accepts (raw : List Bool) (f : Fields) (h : separate raw = some f) :
    RunsExactly step (cfg lab.outerScan memory (tapes st frame raw [] [] []))
      (cfg lab.good memory (tapes st frame f.denominator f.magnitude [f.negative] []))
      (2 * f.magnitude.length + 14) := by
  obtain ⟨rfl, hd⟩ := separate_some h
  exact accepts_exact step st lab exec memory frame f hd

theorem outer_reject (raw : List Bool) (h : Encoding.unframe raw = none) :
    ∃ (produced : List Bool) (time : ℕ), time ≤ raw.length + 1 ∧ produced.length ≤ raw.length ∧
      RunsExactly step (cfg lab.outerScan memory (tapes st frame raw [] [] []))
        (cfg lab.bad memory (tapes st frame [] [] [] produced.reverse)) time := by
  rw [Contract.unframe_eq] at h
  simpa only [tapes, List.append_nil] using
    GraphPreprocessing.Frame.rejects (st 0) (st 1) (st 3)
      (neq st 0 1 (by decide)) (neq st 0 3 (by decide))
      step lab.outerScan lab.outerRestore lab.bad exec.outerScan memory
      (Function.update frame (st 2) []) raw [] [] h

theorem inner_reject (integer denominator : List Bool) (h : Encoding.unframe integer = none) :
    ∃ (produced : List Bool) (time : ℕ), time ≤ integer.length + 1 ∧ produced.length ≤ integer.length ∧
      RunsExactly step (cfg lab.signScan memory (tapes st frame denominator integer [] []))
        (cfg lab.bad memory (tapes st frame denominator [] [] produced.reverse)) time := by
  rw [Contract.unframe_eq] at h
  simpa only [tapes_inner, List.append_nil] using
    GraphPreprocessing.Frame.rejects (st 1) (st 2) (st 3)
      (neq st 1 2 (by decide)) (neq st 1 3 (by decide))
      step lab.signScan lab.signRestore lab.bad exec.signScan memory
      (Function.update frame (st 0) denominator) integer [] [] h

omit exec in
private theorem unframe_layout {raw word rest : List Bool}
    (h : Encoding.unframe raw = some (word, rest)) : raw = Encoding.frame word ++ rest := by
  rw [Contract.unframe_eq] at h
  simpa only [Contract.frame_eq] using
    (GraphPreprocessing.Frame.unframe_some_iff raw word rest).mp h

/-- Every rejection branch returns in linear time. The theorem exposes the
residual store and preserves every stack outside the four selected positions. -/
theorem rejects (raw : List Bool) (h : separate raw = none) :
    ∃ (ending : K → List Bool) (time : ℕ), time ≤ 2 * raw.length + 8 ∧
      RunsExactly step (cfg lab.outerScan memory (tapes st frame raw [] [] []))
        (cfg lab.bad memory ending) time ∧
      ∀ k, (∀ i : Fin 4, k ≠ st i) → ending k = frame k := by
  cases ho : Encoding.unframe raw with
  | none =>
    obtain ⟨produced, time, ht, _, hr⟩ := outer_reject step st lab exec memory frame raw ho
    exact ⟨_, time, by omega, hr, tapes_other st frame [] [] [] produced.reverse⟩
  | some p =>
    rcases p with ⟨integer, denominator⟩
    have hl := unframe_layout ho
    have hlen : raw.length = 2 * integer.length + 1 + denominator.length := by
      rw [hl]; simp only [List.length_append, Encoding.frame_length]
    have r1 := outer_exact step st lab exec memory frame integer denominator
    rw [← hl] at r1
    cases hi : Encoding.unframe integer with
    | none =>
      obtain ⟨produced, time, ht, _, hr⟩ := inner_reject step st lab exec memory frame integer denominator hi
      refine ⟨_, time + 2 * (integer.length + 1), by omega, r1.trans hr, ?_⟩
      exact tapes_other st frame denominator [] [] produced.reverse
    | some p =>
      rcases p with ⟨sign, magnitude⟩
      have hil := unframe_layout hi
      have hilen : integer.length = 2 * sign.length + 1 + magnitude.length := by
        rw [hil]; simp only [List.length_append, Encoding.frame_length]
      have r2 := inner_exact step st lab exec memory frame sign magnitude denominator
      rw [← hil] at r2
      have r3 := runsExactly_one (sign_step step st lab exec memory frame sign magnitude denominator)
      by_cases hs : sign.length = 1
      · obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hs
        have hd : denominator = [] := by
          by_contra hd
          simp [separate, ho, hi, bool_decode, hd] at h
        subst denominator
        simp only [List.length_singleton, ↓reduceIte] at r3
        have r4 := runsExactly_one (den_step step st lab exec memory frame [b] magnitude [])
        simp only [↓reduceIte] at r4
        refine ⟨_, 1 + (1 + (2 * ([b].length + 1) + 2 * (integer.length + 1))),
          by simp only [List.length_singleton] at *; omega,
          ((r1.trans r2).trans r3).trans r4, ?_⟩
        exact tapes_other st frame [] magnitude [b] []
      · simp only [ite_eq_right hs] at r3
        refine ⟨_, 1 + (2 * (sign.length + 1) + 2 * (integer.length + 1)),
          by omega, (r1.trans r2).trans r3, ?_⟩
        exact tapes_other st frame denominator magnitude sign []

/-- All raw words reach the matching success/failure continuation with finite
caller memory preserved. No scalar decoding is needed to execute this run. -/
theorem terminates (raw : List Bool) :
    ∃ (ending : K → List Bool) (time : ℕ), time ≤ 2 * raw.length + 8 ∧
      RunsExactly step (cfg lab.outerScan memory (tapes st frame raw [] [] []))
        (cfg (if (separate raw).isSome then lab.good else lab.bad) memory ending) time ∧
      (∀ k, (∀ i : Fin 4, k ≠ st i) → ending k = frame k) ∧
      (∀ f, separate raw = some f → ending = tapes st frame f.denominator f.magnitude [f.negative] []) := by
  cases hs : separate raw with
  | none =>
    obtain ⟨ending, time, ht, hr, hf⟩ := rejects step st lab exec memory frame raw hs
    exact ⟨ending, time, ht, by simpa using hr, hf, by intro f h; simp at h⟩
  | some f =>
    have hr := accepts step st lab exec memory frame raw f hs
    have hl := (separate_some hs).1
    have ht : 2 * f.magnitude.length + 14 ≤ 2 * raw.length + 8 := by
      rw [hl]
      simp only [join, List.length_append, Encoding.frame_length, List.length_singleton]
      omega
    refine ⟨_, _, ht, by simpa using hr,
      tapes_other st frame f.denominator f.magnitude [f.negative] [], ?_⟩
    intro other h
    have he : other = f := Option.some.inj h.symm
    subst other
    rfl

end Returning

/-- A concrete finite instance, independent of the surrounding parser. -/
def localStacks : Stacks (Fin 4) := ⟨id, fun _ _ h => h⟩

def localLabels : Labels (Fin 8) := ⟨0, 1, 2, 3, 4, 5, 6, 7⟩

def program (label : Fin 8) : Stmt (Fin 4) (Fin 8) Unit :=
  if label = 0 then GraphPreprocessing.Frame.scanStmt 0 3 0 1 7
  else if label = 1 then copyMoveStmt 3 1 1 2
  else if label = 2 then GraphPreprocessing.Frame.scanStmt 1 3 2 3 7
  else if label = 3 then copyMoveStmt 3 2 3 4
  else if label = 4 then singletonStmt 2 5 7
  else if label = 5 then denominatorStmt 0 6 7
  else halt

abbrev computer : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Fin 8
  main := 0
  σ := Option Bool × Unit
  initialState := (none, ())
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) :=
  inferInstanceAs (Fintype Bool)

/-- Statement size is uniformly bounded; a transition never performs an
unbounded scalar operation. The count uses H1’s syntactic instruction budget. -/
theorem statement_budget (label : Fin 8) :
    Holant.Complexity.TM2Cost.budget (program label) ≤ 10 := by
  fin_cases label <;> decide

theorem computer_executes : Executes computer.step localStacks localLabels := by
  constructor <;> intro state tape <;> rfl

theorem cfg_init (raw : List Bool) :
    cfg (0 : Fin 8) () (tapes localStacks (fun _ => []) raw [] [] []) = initList computer raw := by
  unfold cfg initList
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Actual four-stack finite-machine acceptance, with exact transition count. -/
theorem computer_accepts (raw : List Bool) (f : Fields) (h : separate raw = some f) :
    RunsExactly computer.step (initList computer raw)
      (cfg (6 : Fin 8) () (tapes localStacks (fun _ => []) f.denominator f.magnitude [f.negative] []))
      (2 * f.magnitude.length + 14) := by
  simpa only [localLabels, cfg_init] using
    accepts computer.step localStacks localLabels computer_executes () (fun _ => []) raw f h

/-- Actual finite-machine termination on every raw rational field. The return
label carries validity; returning does not conflate it with normalized output. -/
theorem computer_terminates (raw : List Bool) :
    ∃ (ending : Fin 4 → List Bool) (time : ℕ), time ≤ 2 * raw.length + 8 ∧
      RunsExactly computer.step (initList computer raw)
        (cfg (if (separate raw).isSome then (6 : Fin 8) else 7) () ending) time := by
  obtain ⟨ending, time, ht, hr, _, _⟩ :=
    terminates computer.step localStacks localLabels computer_executes () (fun _ => []) raw
  exact ⟨ending, time, ht, by simpa only [localLabels, cfg_init] using hr⟩

/-- In the standalone instance either return continuation executes `halt`. -/
theorem return_halts (good : Bool) (saved : Fin 4 → List Bool) :
    computer.step (cfg (if good then 6 else 7) () saved) =
      some (⟨none, (none, ()), saved⟩ : computer.Cfg) := by
  cases good <;> rfl

/-- All words really halt in the bundled instance. This keeps the disclosed
multistack output/residue; it does not serialize or normalize a rational. -/
theorem computer_halts (raw : List Bool) :
    ∃ (saved : Fin 4 → List Bool) (time : ℕ), time ≤ 2 * raw.length + 9 ∧
      RunsExactly computer.step (initList computer raw)
        (⟨none, (none, ()), saved⟩ : computer.Cfg) time := by
  obtain ⟨saved, time, ht, hr⟩ := computer_terminates raw
  exact ⟨saved, 1 + time, by omega,
    hr.trans (runsExactly_one (return_halts (separate raw).isSome saved))⟩

end Counting.Algorithm.KarpLubyRequest.RationalFields
