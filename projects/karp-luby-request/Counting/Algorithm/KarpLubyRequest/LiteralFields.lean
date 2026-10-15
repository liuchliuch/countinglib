import Counting.Algorithm.KarpLubyRequest.BoundedIndex
import Counting.Algorithm.KarpLubyRequest.RationalFields

/-!
# Raw literal parsing with a physically bounded index check

The index frame, singleton polarity, total raw-natural codec, copied variable
header, and binary range loop are real finite-stack stages. The original unary
header stays on its caller stack. No decoded index controls an unbounded loop.
-/
namespace Counting.Algorithm.KarpLubyRequest.LiteralFields

open Turing Computability
open Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby

structure Fields where
  index : List Bool
  polarity : Bool
  deriving DecidableEq

def separate (n : ℕ) (raw : List Bool) : Option Fields := do
  let (index, sign) ← Encoding.unframe raw
  let polarity ← Encoding.bool.decode sign
  if decodeNat index < n then some ⟨index, polarity⟩ else none

/-- Original checked finite-index decoding, with raw natural words preserved. -/
theorem literal_decode_eq (n : ℕ) (raw : List Bool) :
    ((Encoding.literal n).decode raw).map (fun p => (p.1.val, p.2)) =
      (separate n raw).map (fun f => (decodeNat f.index, f.polarity)) := by
  cases hu : Encoding.unframe raw with
  | none => simp [Encoding.literal, Encoding.prod, separate, hu]
  | some p =>
    rcases p with ⟨index, sign⟩
    cases hb : Encoding.bool.decode sign <;> by_cases h : decodeNat index < n <;>
      simp [Encoding.literal, Encoding.prod, Encoding.nat, separate, hu, hb, h]

variable {K Λ τ : Type} [DecidableEq K]

/-- source/polarity, raw index, canonical counter, scratch, unary work,
untouched original variable word. -/
abbrev Stacks (K : Type) := Fin 6 ↪ K

def tapes (st : Stacks K) (frame : K → List Bool)
    (source rawIndex counter scratch unary original : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update frame (st 0) source) (st 1) rawIndex)
      (st 2) counter) (st 3) scratch) (st 4) unary) (st 5) original

structure Labels (Λ : Type) where
  scan : Λ
  restore : Λ
  sign : Λ
  naturalMove : Λ
  naturalHighest : Λ
  naturalRestore : Λ
  copy : Λ
  copyRestore : Λ
  loop : Λ
  borrow : Λ
  rangeRestore : Λ
  good : Λ
  bad : Λ

def naturalStacks (st : Stacks K) : NaturalWords.Stacks K :=
  ⟨fun i => st (![1, 2, 3] i), by
    intro a b h
    have hi := st.injective h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def naturalLabels (lab : Labels Λ) : NaturalWords.Labels Λ :=
  ⟨lab.naturalMove, lab.naturalHighest, lab.naturalRestore, lab.copy⟩

def rangeStacks (st : Stacks K) : BoundedIndex.Stacks K :=
  ⟨fun i => st (![4, 2, 3] i), by
    intro a b h
    have hi := st.injective h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def rangeLabels (lab : Labels Λ) : BoundedIndex.Labels Λ :=
  ⟨lab.loop, lab.borrow, lab.rangeRestore, lab.good, lab.bad⟩

@[simp] theorem natural_zero (st : Stacks K) : naturalStacks st 0 = st 1 := rfl
@[simp] theorem natural_one (st : Stacks K) : naturalStacks st 1 = st 2 := rfl
@[simp] theorem natural_two (st : Stacks K) : naturalStacks st 2 = st 3 := rfl
@[simp] theorem range_zero (st : Stacks K) : rangeStacks st 0 = st 4 := rfl
@[simp] theorem range_one (st : Stacks K) : rangeStacks st 1 = st 2 := rfl
@[simp] theorem range_two (st : Stacks K) : rangeStacks st 2 = st 3 := rfl

structure Executes (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (st : Stacks K) (lab : Labels Λ) : Prop where
  scan : ExecutesAt step lab.scan (Frame.scanStmt (st 0) (st 3) lab.scan lab.restore lab.bad)
  restore : ExecutesAt step lab.restore (copyMoveStmt (st 3) (st 1) lab.restore lab.sign)
  sign : ExecutesAt step lab.sign (RationalFields.singletonStmt (st 0) lab.naturalMove lab.bad)
  natural : NaturalWords.Executes step (naturalStacks st) (naturalLabels lab)
  copy : ExecutesAt step lab.copy (copyMoveStmt (st 5) (st 3) lab.copy lab.copyRestore)
  copyRestore : ExecutesAt step lab.copyRestore
    (copyRestoreStmt (st 5) (st 4) (st 3) lab.copyRestore lab.loop)
  range : BoundedIndex.Executes step (rangeStacks st) (rangeLabels lab)

private theorem as_frame (st : Stacks K) (frame : K → List Bool)
    (source rawIndex counter scratch unary original : List Bool) :
    tapes st frame source rawIndex counter scratch unary original =
      tapes3 (tapes st frame [] [] counter [] unary original) (st 0) (st 1) (st 3)
        source rawIndex scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    by_cases h4 : k = st 4 <;> by_cases h5 : k = st 5 <;>
    simp_all [tapes, tapes3, st.injective.eq_iff]

private theorem as_natural (st : Stacks K) (frame : K → List Bool)
    (source rawIndex counter scratch unary original : List Bool) :
    tapes st frame source rawIndex counter scratch unary original =
      NaturalWords.tapes (naturalStacks st) (tapes st frame source [] [] [] unary original)
        rawIndex counter scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    by_cases h4 : k = st 4 <;> by_cases h5 : k = st 5 <;>
    simp_all [tapes, NaturalWords.tapes, tapes3, st.injective.eq_iff]

private theorem as_copy (st : Stacks K) (frame : K → List Bool)
    (source rawIndex counter scratch unary original : List Bool) :
    tapes st frame source rawIndex counter scratch unary original =
      tapes3 (tapes st frame source rawIndex counter [] [] []) (st 5) (st 4) (st 3)
        original unary scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    by_cases h4 : k = st 4 <;> by_cases h5 : k = st 5 <;>
    simp_all [tapes, tapes3, st.injective.eq_iff]

private theorem as_range (st : Stacks K) (frame : K → List Bool)
    (source rawIndex counter scratch unary original : List Bool) :
    tapes st frame source rawIndex counter scratch unary original =
      BoundedIndex.tapes (rangeStacks st) (tapes st frame source rawIndex [] [] [] original)
        unary counter scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    by_cases h4 : k = st 4 <;> by_cases h5 : k = st 5 <;>
    simp_all [tapes, BoundedIndex.tapes, tapes3, st.injective.eq_iff]

section Returning
variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (st : Stacks K) (lab : Labels Λ)
variable (exec : Executes step st lab) (memory : τ) (frame : K → List Bool)
include exec

theorem frame_exact (index sign original : List Bool) :
    RunsExactly step (cfg lab.scan memory (tapes st frame (Encoding.frame index ++ sign) [] [] [] [] original))
      (cfg lab.sign memory (tapes st frame sign index [] [] [] original)) (2 * (index.length + 1)) := by
  simpa only [← as_frame, Contract.frame_eq, List.append_nil] using
    Frame.extract_exact (st 0) (st 1) (st 3)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      step lab.scan lab.restore lab.sign lab.bad exec.scan exec.restore memory
      (tapes st frame [] [] [] [] [] original) index sign []

theorem sign_step (index sign original : List Bool) :
    step (cfg lab.sign memory (tapes st frame sign index [] [] [] original)) =
      some (cfg (if sign.length = 1 then lab.naturalMove else lab.bad) memory
        (tapes st frame sign index [] [] [] original)) := by
  have h := RationalFields.singleton_step step (st 0) lab.sign lab.naturalMove lab.bad
    exec.sign memory (tapes st frame sign index [] [] [] original) sign
  have hu : Function.update (tapes st frame sign index [] [] [] original) (st 0) sign =
      tapes st frame sign index [] [] [] original := by
    funext k
    by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
      by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
      by_cases h4 : k = st 4 <;> by_cases h5 : k = st 5 <;>
      simp_all [tapes, st.injective.eq_iff]
  simpa only [hu] using h

theorem natural_exact (index sign original : List Bool) :
    RunsExactly step (cfg lab.naturalMove memory (tapes st frame sign index [] [] [] original))
      (cfg lab.copy memory (tapes st frame sign [] (encodeNat (decodeNat index)) [] [] original))
      (2 * index.length + 3) := by
  simpa only [← as_natural, naturalLabels, NaturalWords.canonicalize_eq, List.append_nil] using
    NaturalWords.canonicalize_exact step (naturalStacks st) (naturalLabels lab) exec.natural memory
      (tapes st frame sign [] [] [] [] original) index []

theorem copy_exact (sign counter original : List Bool) :
    RunsExactly step (cfg lab.copy memory (tapes st frame sign [] counter [] [] original))
      (cfg lab.loop memory (tapes st frame sign [] counter [] original original))
      (2 * (original.length + 1)) := by
  simpa only [← as_copy, List.append_nil] using
    copy_exact_frame (st 5) (st 4) (st 3)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      step lab.copy lab.copyRestore lab.loop exec.copy exec.copyRestore memory
      (tapes st frame sign [] counter [] [] []) original []

/-- One actual sequence reads the raw index, checks polarity, normalizes exactly
its original decoded value, copies the physical variable word, and tests range. -/
theorem checked (index : List Bool) (polarity : Bool) (original : List Bool) :
    ∃ (remaining counter : List Bool) (time : ℕ),
      time ≤ 4 * index.length + 2 * original.length + 8 +
        (original.length + 1) * (2 * (index.length + 1) + 3) ∧
      RunsExactly step
        (cfg lab.scan memory (tapes st frame (Encoding.frame index ++ [polarity]) [] [] [] [] original))
        (cfg (if decodeNat index < original.length then lab.good else lab.bad) memory
          (tapes st frame [polarity] [] counter [] remaining original)) time ∧
      (decodeNat index < original.length →
        remaining = original.drop (decodeNat index + 1) ∧ counter = []) := by
  have r1 := frame_exact step st lab exec memory frame index [polarity] original
  have r2 := runsExactly_one (sign_step step st lab exec memory frame index [polarity] original)
  simp only [List.length_singleton, ↓reduceIte] at r2
  have r3 := natural_exact step st lab exec memory frame index [polarity] original
  have r4 := copy_exact step st lab exec memory frame [polarity] (encodeNat (decodeNat index)) original
  obtain ⟨remaining, counter, time, ht, hr, hs⟩ := BoundedIndex.terminates step (rangeStacks st)
    (rangeLabels lab) exec.range memory (tapes st frame [polarity] [] [] [] [] original)
    original (decodeNat index)
  have rr : RunsExactly step (cfg lab.loop memory
      (tapes st frame [polarity] [] (encodeNat (decodeNat index)) [] original original))
      (cfg (if decodeNat index < original.length then lab.good else lab.bad) memory
        (tapes st frame [polarity] [] counter [] remaining original)) time := by
    simpa only [← as_range, rangeLabels] using hr
  have hn := (NaturalWords.canonicalize_length index).2
  rw [NaturalWords.canonicalize_eq] at hn
  refine ⟨remaining, counter, time + (2 * (original.length + 1) +
    ((2 * index.length + 3) + (1 + 2 * (index.length + 1)))), ?_, ?_, hs⟩
  · nlinarith
  · exact (((r1.trans r2).trans r3).trans r4).trans rr


/-- Successful raw parsing gives the exact clean index and scratch stacks and
remaining physical variable suffix needed by a sequential caller. -/
theorem accepts (raw original : List Bool) (f : Fields)
    (h : separate original.length raw = some f) :
    ∃ time, time ≤ 4 * raw.length + 2 * original.length + 8 +
        (original.length + 1) * (2 * raw.length + 5) ∧
      RunsExactly step (cfg lab.scan memory (tapes st frame raw [] [] [] [] original))
        (cfg lab.good memory (tapes st frame [f.polarity] [] [] []
          (original.drop (decodeNat f.index + 1)) original)) time := by
  cases hu : Encoding.unframe raw with
  | none => simp [separate, hu] at h
  | some pair =>
    rcases pair with ⟨index, sign⟩
    cases hb : Encoding.bool.decode sign with
    | none => simp [separate, hu, hb] at h
    | some polarity =>
      have he : sign = [polarity] := by
        cases sign with
        | nil => simp [RationalFields.bool_decode] at hb
        | cons b tail => cases tail <;> simp_all [RationalFields.bool_decode]
      subst sign
      by_cases hi : decodeNat index < original.length
      · simp [separate, hu, hb, hi] at h
        subst f
        have hp : raw = Encoding.frame index ++ [polarity] := by
          rw [Contract.unframe_eq] at hu
          simpa only [Contract.frame_eq] using (Frame.unframe_some_iff _ _ _).mp hu
        obtain ⟨remaining, counter, time, ht, hr, hs⟩ :=
          checked step st lab exec memory frame index polarity original
        obtain ⟨rfl, rfl⟩ := hs hi
        simp only [if_pos hi] at hr
        rw [← hp] at hr
        refine ⟨time, ?_, hr⟩
        have hl := congrArg List.length hp
        simp only [List.length_append, Encoding.frame_length, List.length_singleton] at hl
        nlinarith
      · simp [separate, hu, hb, hi] at h


def timeBound (rawLength variablesLength : ℕ) : ℕ :=
  4 * rawLength + 2 * variablesLength + 8 +
    (variablesLength + 1) * (2 * rawLength + 5)

omit exec in
private theorem singleton_iff (sign : List Bool) : sign.length = 1 ↔ ∃ b, sign = [b] := by
  cases sign with
  | nil => simp
  | cons b tail => cases tail <;> simp

omit exec in
private theorem bool_none (sign : List Bool) (h : sign.length ≠ 1) :
    Encoding.bool.decode sign = none := by
  cases sign with
  | nil => rfl
  | cons b tail =>
    cases tail with
    | nil => simp at h
    | cons c rest => rfl

/-- Complete raw literal validation, including every malformed frame, wrong
polarity length, and out-of-range index. The original variable word is a real
input stack and its copy and each range-loop access are part of this run. -/
theorem terminates (raw original : List Bool) :
    ∃ (ending : K → List Bool) (time : ℕ), time ≤ timeBound raw.length original.length ∧
      RunsExactly step (cfg lab.scan memory (tapes st frame raw [] [] [] [] original))
        (cfg (if (separate original.length raw).isSome then lab.good else lab.bad) memory ending) time := by
  cases hu : Encoding.unframe raw with
  | none =>
    have hu' := hu
    rw [Contract.unframe_eq] at hu'
    obtain ⟨produced, time, ht, _, hr⟩ := Frame.rejects (st 0) (st 1) (st 3)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      step lab.scan lab.restore lab.bad exec.scan memory
      (tapes st frame [] [] [] [] [] original) raw [] [] hu'
    refine ⟨tapes st frame [] [] [] produced.reverse [] original, time, ?_, ?_⟩
    · unfold timeBound; nlinarith
    · simpa [← as_frame, List.append_nil, separate, hu] using hr
  | some pair =>
    rcases pair with ⟨index, sign⟩
    have hp : raw = Encoding.frame index ++ sign := by
      have h := hu
      rw [Contract.unframe_eq] at h
      simpa only [Contract.frame_eq] using (Frame.unframe_some_iff _ _ _).mp h
    have hl := congrArg List.length hp
    simp only [List.length_append, Encoding.frame_length] at hl
    by_cases hs : sign.length = 1
    · obtain ⟨polarity, rfl⟩ := (singleton_iff sign).mp hs
      obtain ⟨remaining, counter, time, ht, hr, _⟩ := checked step st lab exec memory frame index polarity original
      refine ⟨tapes st frame [polarity] [] counter [] remaining original, time, ?_, ?_⟩
      · unfold timeBound; simp only [List.length_singleton] at hl; nlinarith
      · rw [← hp] at hr
        by_cases hh : decodeNat index < original.length <;>
          simpa [separate, hu, RationalFields.bool_decode, hh] using hr
    · have r1 := frame_exact step st lab exec memory frame index sign original
      have r2 := runsExactly_one (sign_step step st lab exec memory frame index sign original)
      simp only [ite_eq_right hs] at r2
      have hr := r1.trans r2
      rw [← hp] at hr
      refine ⟨tapes st frame sign index [] [] [] original, 1 + 2 * (index.length + 1), ?_, ?_⟩
      · unfold timeBound; nlinarith
      · simpa [separate, hu, bool_none sign hs] using hr

end Returning

/-- Six finite Boolean stacks and thirteen finite program labels. -/
def localStacks : Stacks (Fin 6) := ⟨id, fun _ _ h => h⟩
def localLabels : Labels (Fin 13) := ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12⟩

def program (label : Fin 13) : Stmt (Fin 6) (Fin 13) Bool :=
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
  else if label = 11 then .load (fun _ => (none, true)) .halt
  else .load (fun _ => (none, false)) .halt

abbrev computer : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 0
  Γ _ := Bool
  Λ := Fin 13
  main := 0
  σ := Option Bool × Bool
  initialState := (none, false)
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) :=
  inferInstanceAs (Fintype Bool)

theorem statement_budget (label : Fin 13) : TM2Cost.budget (program label) ≤ 10 := by
  fin_cases label <;> decide

theorem computer_executes : Executes computer.step localStacks localLabels := by
  constructor
  · intro state stk; rfl
  · intro state stk; rfl
  · intro state stk; rfl
  · constructor <;> intro state stk <;> rfl
  · intro state stk; rfl
  · intro state stk; rfl
  · constructor <;> intro state stk <;> rfl

/-- Explicit calling convention: raw literal at stack zero, actual ambient
variable word at stack five, and empty owned workspaces. -/
def initial (raw original : List Bool) : computer.Cfg :=
  cfg 0 false (tapes localStacks (fun _ => []) raw [] [] [] [] original)

theorem computer_returns (raw original : List Bool) :
    ∃ (ending : Fin 6 → List Bool) (time : ℕ), time ≤ timeBound raw.length original.length ∧
      RunsExactly computer.step (initial raw original)
        (cfg (if (separate original.length raw).isSome then 11 else 12) false ending) time := by
  simpa only [localLabels, initial] using
    terminates computer.step localStacks localLabels computer_executes false (fun _ => []) raw original

theorem return_halts (good : Bool) (ending : Fin 6 → List Bool) :
    computer.step (cfg (if good then 11 else 12) false ending) =
      some (⟨none, (none, good), ending⟩ : computer.Cfg) := by
  cases good <;> rfl

theorem computer_halts (raw original : List Bool) :
    ∃ (ending : Fin 6 → List Bool) (time : ℕ), time ≤ timeBound raw.length original.length + 1 ∧
      RunsExactly computer.step (initial raw original)
        (⟨none, (none, (separate original.length raw).isSome), ending⟩ : computer.Cfg) time := by
  obtain ⟨ending, time, ht, hr⟩ := computer_returns raw original
  exact ⟨ending, 1 + time, by omega,
    hr.trans (runsExactly_one (return_halts (separate original.length raw).isSome ending))⟩

theorem computer_bit_cost (raw original : List Bool) :
    ∃ (ending : Fin 6 → List Bool) (time : ℕ), time ≤ timeBound raw.length original.length + 1 ∧
      (Primitive.run program time (some (initial raw original))).2 =
        some (⟨none, (none, (separate original.length raw).isSome), ending⟩ : computer.Cfg) ∧
      (Primitive.run program time (some (initial raw original))).1 ≤
        10 * (timeBound raw.length original.length + 1) := by
  obtain ⟨ending, time, ht, hr⟩ := computer_halts raw original
  have hc := Primitive.execution_cost program 10 statement_budget time (initial raw original)
    (⟨none, (none, (separate original.length raw).isSome), ending⟩ : computer.Cfg) hr
  exact ⟨ending, time, ht, hc.1, hc.2.trans (Nat.mul_le_mul_left 10 ht)⟩

end Counting.Algorithm.KarpLubyRequest.LiteralFields
