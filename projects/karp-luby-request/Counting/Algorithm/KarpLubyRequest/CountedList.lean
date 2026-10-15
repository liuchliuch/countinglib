import Counting.Algorithm.KarpLubyRequest.ListFields
import Holant.Complexity.IntegerArithmetic.CarryBits
import Holant.Complexity.GraphPreprocessing.ListScan
import Holant.Complexity.GraphPreprocessing.Primitive
import Mathlib.Tactic.Linarith

/-!
# Physically bounded list validation with a binary countdown

The natural counter uses H1's unique `IntegerArithmetic.decrement` specification
and its canonical arithmetic theorems. This module supplies the returning
`Option Bool × τ` implementation needed by the raw request caller; H1's existing
signed-arithmetic implementation uses a different fixed control-memory type.
Payload traversal reuses H1's actual framing skip routine. Every countdown is
preceded by consumption of an actual framed element, so an enormous decoded
header cannot create an exponentially long empty loop.
-/
namespace Counting.Algorithm.KarpLubyRequest.CountedList

open Turing Computability
open Turing.TM2.Stmt
open Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby
open Holant.Complexity.IntegerArithmetic

namespace Counter
variable {K Λ τ : Type} [DecidableEq K]

/-- The finite borrow state is the loop label. Only one optional bit is in memory. -/
def decrementStmt (src tmp : K) (loop restore : Λ) : Stmt K Λ τ :=
  pop src (fun v b => (b, v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (peek src (fun v b => (b, v.2))
          (branch (fun v => v.1.isSome)
            (push src (fun _ => false)
              (load (fun v => (none, v.2)) (goto (fun _ => restore))))
            (load (fun v => (none, v.2)) (goto (fun _ => restore)))))
        (push tmp (fun _ => true)
          (load (fun v => (none, v.2)) (goto (fun _ => loop)))))
      (load (fun v => (none, v.2)) (goto (fun _ => restore))))

omit [DecidableEq K] in
theorem statement_budget (src tmp : K) (loop restore : Λ) :
    TM2Cost.budget (decrementStmt (τ := τ) src tmp loop restore) = 8 := rfl

variable (src spare tmp : K) (hsd : src ≠ spare) (hst : src ≠ tmp) (hdt : spare ≠ tmp)
variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (loop restore next : Λ)
variable (exec : ExecutesAt step loop (decrementStmt src tmp loop restore))
variable (memory : τ) (frame : K → List Bool)

include exec hsd hst in
theorem false_step (word saved scratch : List Bool) :
    step (cfg loop memory (tapes3 frame src spare tmp (false :: word) saved scratch)) =
      some (cfg loop memory (tapes3 frame src spare tmp word saved (true :: scratch))) := by
  rw [cfg, exec]
  simp [decrementStmt, TM2.stepAux, cfg, tapes3_src src spare tmp hsd hst,
    update_tapes3_src src spare tmp hsd hst]

include exec hsd hst in
theorem true_step (word saved scratch : List Bool) :
    step (cfg loop memory (tapes3 frame src spare tmp (true :: word) saved scratch)) =
      some (cfg restore memory (tapes3 frame src spare tmp
        (Holant.Complexity.BinaryArithmetic.Doubling.shift word) saved scratch)) := by
  cases word <;> rw [cfg, exec] <;>
    simp [decrementStmt, TM2.stepAux, cfg, tapes3_src src spare tmp hsd hst,
      update_tapes3_src src spare tmp hsd hst, Holant.Complexity.BinaryArithmetic.Doubling.shift]

include exec hsd hst in
theorem nil_step (saved scratch : List Bool) :
    step (cfg loop memory (tapes3 frame src spare tmp [] saved scratch)) =
      some (cfg restore memory (tapes3 frame src spare tmp [] saved scratch)) := by
  rw [cfg, exec]
  simp [decrementStmt, TM2.stepAux, cfg, tapes3_src src spare tmp hsd hst,
    update_tapes3_src src spare tmp hsd hst]

include exec hsd hst in
/-- Each propagated borrow is a real transition and pushes one physical bit. -/
theorem borrow_exact (word saved scratch : List Bool) :
    RunsExactly step (cfg loop memory (tapes3 frame src spare tmp word saved scratch))
      (cfg restore memory (tapes3 frame src spare tmp (borrowTail word) saved
        (List.replicate (borrowCount word) true ++ scratch))) (borrowCount word + 1) := by
  induction word generalizing scratch with
  | nil => simpa [borrowTail, borrowCount] using
      (runsExactly_one (nil_step src spare tmp hsd hst step loop restore exec memory frame saved scratch))
  | cons bit word ih =>
    cases bit
    · have run := (runsExactly_one
        (false_step src spare tmp hsd hst step loop restore exec memory frame word saved scratch)).trans
          (ih (true :: scratch))
      simpa [borrowTail, borrowCount, List.replicate_add, List.append_assoc] using run
    · simpa [borrowTail, borrowCount] using
        (runsExactly_one (true_step src spare tmp hsd hst step loop restore exec memory frame word saved scratch))

include hsd hst hdt in
private theorem swap_tapes (word saved scratch : List Bool) :
    tapes3 frame src spare tmp word saved scratch = tapes3 frame tmp spare src scratch saved word := by
  funext k
  by_cases h0 : k = src <;> by_cases h1 : k = spare <;> by_cases h2 : k = tmp <;>
    simp_all [tapes3]

include exec hsd hst hdt in
/-- Adapted finite-control implementation of the canonical H1 decrement word. -/
theorem decrement_exact (restoreExec : ExecutesAt step restore (copyMoveStmt tmp src restore next))
    (word saved : List Bool) :
    RunsExactly step (cfg loop memory (tapes3 frame src spare tmp word saved []))
      (cfg next memory (tapes3 frame src spare tmp (decrement word) saved []))
      (2 * (borrowCount word + 1)) := by
  have first := borrow_exact src spare tmp hsd hst step loop restore exec memory frame word saved []
  simp only [List.append_nil] at first
  have second : RunsExactly step
      (cfg restore memory (tapes3 frame src spare tmp (borrowTail word) saved
        (List.replicate (borrowCount word) true)))
      (cfg next memory (tapes3 frame src spare tmp (decrement word) saved []))
      (borrowCount word + 1) := by
    have run := copy_move_exact tmp spare src (Ne.symm hdt) (Ne.symm hst)
      step restore next restoreExec memory frame (List.replicate (borrowCount word) true) saved (borrowTail word)
    simpa only [← swap_tapes src spare tmp hsd hst hdt frame, List.reverse_replicate,
      List.length_replicate, ← decrement_split] using run
  convert first.trans second using 1 <;> omega

end Counter

/-- Mathematical contract for exactly `n` raw frames and no unconsumed tail. -/
def body (n : ℕ) (raw : List Bool) : Option (List (List Bool)) := do
  let (words, tail) ← Encoding.unframes n raw
  if tail = [] then some words else none

@[simp] theorem body_zero (raw : List Bool) :
    body 0 raw = if raw = [] then some [] else none := rfl

theorem body_succ (n : ℕ) (raw : List Bool) :
    body (n + 1) raw = do
      let (word, rest) ← Encoding.unframe raw
      let more ← body n rest
      return word :: more := by
  cases h : Encoding.unframe raw with
  | none => simp [body, Encoding.unframes, h]
  | some pair =>
    rcases pair with ⟨word, rest⟩
    cases ht : Encoding.unframes n rest with
    | none => simp [body, Encoding.unframes, h, ht]
    | some pair =>
      rcases pair with ⟨more, tail⟩
      by_cases he : tail = [] <;> simp [body, Encoding.unframes, h, ht, he]

theorem split_eq (raw : List Bool) :
    ListFields.split raw = (Encoding.unframe raw).bind (fun p => body (decodeNat p.1) p.2) := by
  cases h : Encoding.unframe raw <;> simp [ListFields.split, body, h]

theorem body_some_iff (n : ℕ) (raw : List Bool) (words : List (List Bool)) :
    body n raw = some words ↔ words.length = n ∧ raw = Encoding.frames words := by
  constructor
  · intro h
    cases hu : Encoding.unframes n raw with
    | none => simp [body, hu] at h
    | some pair =>
      rcases pair with ⟨found, tail⟩
      by_cases ht : tail = []
      · subst tail
        simp [body, hu] at h
        subst found
        simpa using (ListFields.unframes_some_iff n raw [] words).mp hu
      · simp [body, hu, ht] at h
  · rintro ⟨rfl, rfl⟩
    simp [body]

private theorem nat_succ_nonempty (n : ℕ) : encodeNat (n + 1) ≠ [] := by
  intro h
  have he := congrArg decodeNat h
  rw [decode_encodeNat] at he
  have hz : decodeNat [] = 0 := rfl
  rw [hz] at he
  omega

namespace Body
variable {K Λ τ : Type} [DecidableEq K]

abbrev Stacks (K : Type) := ListFields.Stacks K
abbrev tapes := @ListFields.tapes

structure Labels (Λ : Type) where
  copy : Λ
  copyRestore : Λ
  loop : Λ
  skip : Λ
  borrow : Λ
  restore : Λ
  good : Λ
  bad : Λ

/-- Counter EOF accepts only source EOF. Positive counters enter an actual
framing scan; they are never converted into a finite-control natural number. -/
def checkStmt (src count : K) (skip good bad : Λ) : Stmt K Λ τ :=
  peek count (fun v b => (b, v.2))
    (branch (fun v => v.1.isSome)
      (load (fun v => (none, v.2)) (goto (fun _ => skip)))
      (peek src (fun v b => (b, v.2))
        (branch (fun v => v.1.isSome)
          (load (fun v => (none, v.2)) (goto (fun _ => bad)))
          (load (fun v => (none, v.2)) (goto (fun _ => good))))))

structure Executes (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (st : Stacks K) (lab : Labels Λ) : Prop where
  copy : ExecutesAt step lab.copy (copyMoveStmt (st 0) (st 3) lab.copy lab.copyRestore)
  copyRestore : ExecutesAt step lab.copyRestore
    (copyRestoreStmt (st 0) (st 1) (st 3) lab.copyRestore lab.loop)
  loop : ExecutesAt step lab.loop (checkStmt (st 0) (st 2) lab.skip lab.good lab.bad)
  skip : ExecutesAt step lab.skip
    (GraphPreprocessing.ListScan.skipStmt (st 0) lab.skip lab.borrow lab.bad)
  borrow : ExecutesAt step lab.borrow (Counter.decrementStmt (st 2) (st 3) lab.borrow lab.restore)
  restore : ExecutesAt step lab.restore (copyMoveStmt (st 3) (st 2) lab.restore lab.loop)

private theorem as_skip (st : Stacks K) (frame : K → List Bool)
    (raw output counter scratch : List Bool) :
    tapes st frame raw output counter scratch =
      GraphPreprocessing.ListScan.tapes2
        (Function.update (Function.update frame (st 1) output) (st 3) scratch)
        (st 0) (st 2) raw counter := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    simp_all [tapes, ListFields.tapes, tapes3, GraphPreprocessing.ListScan.tapes2, st.injective.eq_iff]

private theorem as_counter (st : Stacks K) (frame : K → List Bool)
    (raw output counter scratch : List Bool) :
    tapes st frame raw output counter scratch =
      tapes3 (Function.update frame (st 1) output) (st 2) (st 0) (st 3) counter raw scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    simp_all [tapes, ListFields.tapes, tapes3, st.injective.eq_iff]

section Returning
variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (st : Stacks K) (lab : Labels Λ)
variable (exec : Executes step st lab) (memory : τ) (frame : K → List Bool)

include exec

theorem copy_exact (raw counter : List Bool) :
    RunsExactly step (cfg lab.copy memory (tapes st frame raw [] counter []))
      (cfg lab.loop memory (tapes st frame raw raw counter [])) (2 * (raw.length + 1)) := by
  simpa only [tapes, ListFields.tapes, List.append_nil] using
    copy_exact_frame (st 0) (st 1) (st 3)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      step lab.copy lab.copyRestore lab.loop exec.copy exec.copyRestore
      memory (Function.update frame (st 2) counter) raw []

theorem check_zero (raw output : List Bool) :
    step (cfg lab.loop memory (tapes st frame raw output [] [])) =
      some (cfg (if raw = [] then lab.good else lab.bad) memory (tapes st frame raw output [] [])) := by
  rw [cfg, exec.loop]
  cases raw <;> simp [checkStmt, TM2.stepAux, cfg, tapes, ListFields.tapes, tapes3, st.injective.eq_iff]

theorem check_positive (raw output counter : List Bool) (hc : counter ≠ []) :
    step (cfg lab.loop memory (tapes st frame raw output counter [])) =
      some (cfg lab.skip memory (tapes st frame raw output counter [])) := by
  rw [cfg, exec.loop]
  cases counter with
  | nil => contradiction
  | cons b counter =>
    simp [checkStmt, TM2.stepAux, cfg, tapes, ListFields.tapes, tapes3, st.injective.eq_iff]

theorem skip_exact (word rest output counter : List Bool) :
    RunsExactly step (cfg lab.skip memory (tapes st frame (Encoding.frame word ++ rest) output counter []))
      (cfg lab.borrow memory (tapes st frame rest output counter [])) (word.length + 1) := by
  simpa only [as_skip, Contract.frame_eq] using
    GraphPreprocessing.ListScan.skip_exact (st 0) (st 2)
      (fun h => by have := st.injective h; contradiction)
      step lab.skip lab.borrow lab.bad exec.skip memory
      (Function.update (Function.update frame (st 1) output) (st 3) []) word rest counter

theorem skip_rejects (raw output counter : List Bool) (h : Encoding.unframe raw = none) :
    ∃ time, time ≤ raw.length + 1 ∧
      RunsExactly step (cfg lab.skip memory (tapes st frame raw output counter []))
        (cfg lab.bad memory (tapes st frame [] output counter [])) time := by
  rw [Contract.unframe_eq] at h
  simpa only [as_skip] using
    GraphPreprocessing.ListScan.skip_rejects (st 0) (st 2)
      (fun h => by have := st.injective h; contradiction)
      step lab.skip lab.borrow lab.bad exec.skip memory
      (Function.update (Function.update frame (st 1) output) (st 3) []) raw counter h

theorem decrement_exact (raw output counter : List Bool) :
    RunsExactly step (cfg lab.borrow memory (tapes st frame raw output counter []))
      (cfg lab.loop memory (tapes st frame raw output (decrement counter) []))
      (2 * (borrowCount counter + 1)) := by
  simpa only [as_counter] using
    Counter.decrement_exact (st 2) (st 0) (st 3)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      step lab.borrow lab.restore lab.loop exec.borrow memory (Function.update frame (st 1) output)
      exec.restore counter raw

/-- Total real execution, proved by decreasing physical input length. The
binary countdown's numerical magnitude is absent from the time bound. -/
theorem loop_terminates (raw output : List Bool) (n : ℕ) :
    ∃ (remaining counter : List Bool) (time : ℕ),
      time ≤ (raw.length + 1) * (2 * (encodeNat n).length + 4) ∧
      RunsExactly step (cfg lab.loop memory (tapes st frame raw output (encodeNat n) []))
        (cfg (if (body n raw).isSome then lab.good else lab.bad) memory
          (tapes st frame remaining output counter [])) time ∧
      ((body n raw).isSome = true → remaining = [] ∧ counter = []) := by
  generalize hlen : raw.length = length
  induction length using Nat.strong_induction_on generalizing raw n with
  | h length ih =>
    cases n with
    | zero =>
      refine ⟨raw, [], 1, by change 1 ≤ (length + 1) * 4; omega, ?_, ?_⟩
      · by_cases he : raw = [] <;>
          simpa [body_zero, show encodeNat 0 = [] from rfl, he] using
            runsExactly_one (check_zero step st lab exec memory frame raw output)
      · by_cases he : raw = [] <;> simp [he]
    | succ n =>
      have first := runsExactly_one (check_positive step st lab exec memory frame raw output
        (encodeNat (n + 1)) (nat_succ_nonempty n))
      cases hu : Encoding.unframe raw with
      | none =>
        obtain ⟨time, ht, hr⟩ := skip_rejects step st lab exec memory frame raw output (encodeNat (n + 1)) hu
        refine ⟨[], encodeNat (n + 1), time + 1, ?_, ?_, ?_⟩
        · nlinarith
        · simpa [body_succ, hu] using first.trans hr
        · simp [body_succ, hu]
      | some wr =>
        rcases wr with ⟨word, rest⟩
        have hraw : raw = Encoding.frame word ++ rest := by
          rw [Contract.unframe_eq] at hu
          simpa only [Contract.frame_eq] using
            (GraphPreprocessing.Frame.unframe_some_iff _ _ _).mp hu
        have hl := congrArg List.length hraw
        simp only [List.length_append, Encoding.frame_length] at hl
        have hlt : rest.length < raw.length := by omega
        obtain ⟨remaining, counter, time, ht, hr, hs⟩ := ih rest.length (by omega) rest n rfl
        have skip := skip_exact step st lab exec memory frame word rest output (encodeNat (n + 1))
        rw [← hraw] at skip
        have dec := decrement_exact step st lab exec memory frame rest output (encodeNat (n + 1))
        rw [decrement_encodeNat, Nat.add_sub_cancel] at dec
        have whole := ((first.trans skip).trans dec).trans hr
        refine ⟨remaining, counter,
          time + (2 * (borrowCount (encodeNat (n + 1)) + 1) + (word.length + 1 + 1)), ?_, ?_, ?_⟩
        · have hc := borrowCount_le (encodeNat (n + 1))
          have hd := decrement_length_le (encodeNat (n + 1))
          rw [decrement_encodeNat, Nat.add_sub_cancel] at hd
          have hm := Nat.mul_le_mul_left (rest.length + 1)
            (show 2 * (encodeNat n).length + 4 ≤ 2 * (encodeNat (n + 1)).length + 4 by omega)
          nlinarith
        · cases hb : body n rest <;> simpa [body_succ, hu, hb] using whole
        · cases hb : body n rest <;> simpa [body_succ, hu, hb] using hs

/-- The initial copy is executed and charged. Success leaves exactly the
original raw payload in the output stack, preserving all element occurrences. -/
theorem terminates (raw : List Bool) (n : ℕ) :
    ∃ (remaining counter : List Bool) (time : ℕ),
      time ≤ (raw.length + 1) * (2 * (encodeNat n).length + 6) ∧
      RunsExactly step (cfg lab.copy memory (tapes st frame raw [] (encodeNat n) []))
        (cfg (if (body n raw).isSome then lab.good else lab.bad) memory
          (tapes st frame remaining raw counter [])) time ∧
      ((body n raw).isSome = true → remaining = [] ∧ counter = []) := by
  obtain ⟨remaining, counter, time, ht, hr, hs⟩ :=
    loop_terminates step st lab exec memory frame raw raw n
  exact ⟨remaining, counter, time + 2 * (raw.length + 1), by nlinarith,
    (copy_exact step st lab exec memory frame raw (encodeNat n)).trans hr, hs⟩

end Returning
end Body

namespace Full
variable {K Λ τ : Type} [DecidableEq K]
abbrev Stacks (K : Type) := ListFields.Stacks K
abbrev tapes := @ListFields.tapes

structure Labels (Λ : Type) where
  scan : Λ
  extract : Λ
  move : Λ
  highest : Λ
  naturalRestore : Λ
  copy : Λ
  copyRestore : Λ
  loop : Λ
  skip : Λ
  borrow : Λ
  restore : Λ
  good : Λ
  bad : Λ

def headerLabels (lab : Labels Λ) : ListFields.Labels Λ :=
  ⟨lab.scan, lab.extract, lab.move, lab.highest, lab.naturalRestore, lab.copy, lab.bad⟩

def bodyLabels (lab : Labels Λ) : Body.Labels Λ :=
  ⟨lab.copy, lab.copyRestore, lab.loop, lab.skip, lab.borrow, lab.restore, lab.good, lab.bad⟩

structure Executes (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (st : Stacks K) (lab : Labels Λ) : Prop where
  header : ListFields.Executes step st (headerLabels lab)
  body : Body.Executes step st (bodyLabels lab)

/-- A deliberately simple polynomial in total physical input bits. -/
def timeBound (length : ℕ) : ℕ := (length + 1) * (2 * length + 12) + 5

section Returning
variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (st : Stacks K) (lab : Labels Λ)
variable (exec : Executes step st lab) (memory : τ) (frame : K → List Bool)

include exec

/-- All raw words execute through header extraction, normalization, payload
copy, framing checks and binary decrement. Success materializes precisely the
ordered raw element frames used by R1's list decoder. -/
theorem terminates (raw : List Bool) :
    ∃ (ending : K → List Bool) (time : ℕ), time ≤ timeBound raw.length ∧
      RunsExactly step (cfg lab.scan memory (tapes st frame raw [] [] []))
        (cfg (if (ListFields.split raw).isSome then lab.good else lab.bad) memory ending) time ∧
      (∀ k, (∀ i : Fin 4, k ≠ st i) → ending k = frame k) ∧
      (∀ words, ListFields.split raw = some words →
        ending = tapes st frame [] (Encoding.frames words) [] []) := by
  cases hu : Encoding.unframe raw with
  | none =>
    obtain ⟨produced, time, ht, _, hr⟩ :=
      ListFields.header_rejects step st (headerLabels lab) exec.header memory frame raw hu
    refine ⟨_, time, ?_, ?_, ListFields.tapes_other st frame [] [] [] produced.reverse, ?_⟩
    · unfold timeBound; nlinarith
    · simpa [split_eq, hu, tapes, headerLabels] using hr
    · intro words h; simp [split_eq, hu] at h
  | some hp =>
    rcases hp with ⟨word, payload⟩
    have hraw : raw = Encoding.frame word ++ payload := by
      rw [Contract.unframe_eq] at hu
      simpa only [Contract.frame_eq] using
        (GraphPreprocessing.Frame.unframe_some_iff _ _ _).mp hu
    have hl := congrArg List.length hraw
    simp only [List.length_append, Encoding.frame_length] at hl
    have hh := ListFields.header_exact step st (headerLabels lab) exec.header memory frame word payload
    rw [← hraw] at hh
    obtain ⟨remaining, counter, time, ht, hr, hs⟩ :=
      Body.terminates step st (bodyLabels lab) exec.body memory frame payload (decodeNat word)
    refine ⟨_, time + (4 * word.length + 5), ?_, ?_,
      ListFields.tapes_other st frame remaining payload counter [], ?_⟩
    · have hc := (NaturalWords.canonicalize_length word).2
      rw [NaturalWords.canonicalize_eq] at hc
      have hp : payload.length ≤ raw.length := by omega
      have hw : word.length ≤ raw.length := by omega
      have hm := Nat.mul_le_mul
        (show payload.length + 1 ≤ raw.length + 1 by omega)
        (show 2 * (encodeNat (decodeNat word)).length + 6 ≤ 2 * raw.length + 8 by omega)
      unfold timeBound
      nlinarith
    · simpa only [split_eq, hu, Option.bind_some, headerLabels, bodyLabels, tapes, Body.tapes] using hh.trans hr
    · intro words h
      have hb : body (decodeNat word) payload = some words := by simpa [split_eq, hu] using h
      have he := hs (by rw [hb]; rfl)
      obtain ⟨_, hp⟩ := (body_some_iff _ _ _).mp hb
      simp only [he.1, he.2, hp]

end Returning

/-- A finite four-stack parser, with active success and failure continuations. -/
def localStacks : Stacks (Fin 4) := ⟨id, fun _ _ h => h⟩
def localLabels : Labels (Fin 13) := ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12⟩

def program (label : Fin 13) : Stmt (Fin 4) (Fin 13) Unit :=
  if label = 0 then GraphPreprocessing.Frame.scanStmt 0 3 0 1 12
  else if label = 1 then copyMoveStmt 3 1 1 2
  else if label = 2 then copyMoveStmt 1 3 2 3
  else if label = 3 then NaturalWords.highestStmt 3 2 4
  else if label = 4 then copyMoveStmt 3 2 4 5
  else if label = 5 then copyMoveStmt 0 3 5 6
  else if label = 6 then copyRestoreStmt 0 1 3 6 7
  else if label = 7 then Body.checkStmt 0 2 8 11 12
  else if label = 8 then GraphPreprocessing.ListScan.skipStmt 0 8 9 12
  else if label = 9 then Counter.decrementStmt 2 3 9 10
  else if label = 10 then copyMoveStmt 3 2 10 7
  else halt

abbrev computer : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Fin 13
  main := 0
  σ := Option Bool × Unit
  initialState := (none, ())
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) :=
  inferInstanceAs (Fintype Bool)

theorem statement_budget (label : Fin 13) : TM2Cost.budget (program label) ≤ 8 := by
  fin_cases label <;> decide

theorem computer_executes : Executes computer.step localStacks localLabels := by
  constructor
  · constructor
    · intro state tape; rfl
    · intro state tape; rfl
    · constructor <;> intro state tape <;> rfl
  · constructor <;> intro state tape <;> rfl

theorem cfg_init (raw : List Bool) :
    cfg (0 : Fin 13) () (tapes localStacks (fun _ => []) raw [] [] []) = initList computer raw := by
  unfold cfg initList
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Every input reaches the correct validity continuation, and accepted raw
words produce exactly the original list of framed element payloads. -/
theorem computer_terminates (raw : List Bool) :
    ∃ (ending : Fin 4 → List Bool) (time : ℕ), time ≤ timeBound raw.length ∧
      RunsExactly computer.step (initList computer raw)
        (cfg (if (ListFields.split raw).isSome then (11 : Fin 13) else 12) () ending) time ∧
      (∀ words, ListFields.split raw = some words →
        ending = tapes localStacks (fun _ => []) [] (Encoding.frames words) [] []) := by
  obtain ⟨ending, time, ht, hr, _, hs⟩ :=
    terminates computer.step localStacks localLabels computer_executes () (fun _ => []) raw
  exact ⟨ending, time, ht, by simpa only [localLabels, cfg_init] using hr, hs⟩

/-- Accepted raw lists materialize all ordered element frames and clear every
workspace stack, including the fully consumed binary counter. -/
theorem computer_accepts (raw : List Bool) (words : List (List Bool))
    (h : ListFields.split raw = some words) :
    ∃ time, time ≤ timeBound raw.length ∧
      RunsExactly computer.step (initList computer raw)
        (cfg (11 : Fin 13) () (tapes localStacks (fun _ => []) [] (Encoding.frames words) [] [])) time := by
  obtain ⟨ending, time, ht, hr, hs⟩ := computer_terminates raw
  rw [hs words h] at hr
  exact ⟨time, ht, by simpa only [h, Option.isSome_some, ↓reduceIte] using hr⟩

/-- Rejection is a real execution on the same finite program. -/
theorem computer_rejects (raw : List Bool) (h : ListFields.split raw = none) :
    ∃ ending time, time ≤ timeBound raw.length ∧
      RunsExactly computer.step (initList computer raw) (cfg (12 : Fin 13) () ending) time := by
  obtain ⟨ending, time, ht, hr, _⟩ := computer_terminates raw
  exact ⟨ending, time, ht, by simpa only [h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using hr⟩

theorem return_halts (good : Bool) (saved : Fin 4 → List Bool) :
    computer.step (cfg (if good then 11 else 12) () saved) =
      some (⟨none, (none, ()), saved⟩ : computer.Cfg) := by
  cases good <;> rfl

/-- All accepted and malformed inputs really halt; failure residues are explicit
caller data and are not conflated with an empty successful list. -/
theorem computer_halts (raw : List Bool) :
    ∃ (saved : Fin 4 → List Bool) (time : ℕ), time ≤ timeBound raw.length + 1 ∧
      RunsExactly computer.step (initList computer raw)
        (⟨none, (none, ()), saved⟩ : computer.Cfg) time := by
  obtain ⟨saved, time, ht, hr, _⟩ := computer_terminates raw
  exact ⟨saved, 1 + time, by omega,
    hr.trans (runsExactly_one (return_halts (ListFields.split raw).isSome saved))⟩

/-- Actual accumulated primitive instructions, measured by H1's statement
interpreter along the same successful or rejecting machine execution. -/
theorem computer_bit_cost (raw : List Bool) :
    ∃ (saved : Fin 4 → List Bool) (time : ℕ), time ≤ timeBound raw.length + 1 ∧
      (GraphPreprocessing.Primitive.run program time (some (initList computer raw))).2 =
        some (⟨none, (none, ()), saved⟩ : computer.Cfg) ∧
      (GraphPreprocessing.Primitive.run program time (some (initList computer raw))).1 ≤
        8 * (timeBound raw.length + 1) := by
  obtain ⟨saved, time, ht, hr⟩ := computer_halts raw
  have hc := GraphPreprocessing.Primitive.execution_cost program 8 statement_budget
    time (initList computer raw) (⟨none, (none, ()), saved⟩ : computer.Cfg) hr
  exact ⟨saved, time, ht, hc.1, hc.2.trans (Nat.mul_le_mul_left 8 ht)⟩

end Full
end Counting.Algorithm.KarpLubyRequest.CountedList
