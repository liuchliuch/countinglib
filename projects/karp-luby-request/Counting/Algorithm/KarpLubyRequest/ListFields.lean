import Counting.Algorithm.KarpLubyRequest.NaturalWords

/-!
# Raw list fields and an actual length-header stage

The semantic splitter below retains each element's raw word, order and
multiplicity and agrees with R1's list decoder after caller-supplied element
validation. Length headers use the exact total `decodeNat`; they are not required
to be canonical. The finite stage here extracts and canonicalizes that header,
leaving the payload on the input stack. It is a returning stage, not a complete
list parser: scanning/counting the payload and comparing its count are separate
remaining machine obligations.
-/
namespace Counting.Algorithm.KarpLubyRequest.ListFields

open Turing Computability
open Turing.TM2.Stmt
open Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby

/-- Split raw element words; validation of individual elements belongs to the caller. -/
def split (raw : List Bool) : Option (List (List Bool)) := do
  let (header, payload) ← Encoding.unframe raw
  let (words, tail) ← Encoding.unframes (decodeNat header) payload
  if tail = [] then some words else none

/-- The original list codec factors through exactly this raw splitter. -/
theorem list_decode_eq {α : Type} (e : Encoding.BitEncoding α) (raw : List Bool) :
    (Encoding.list e).decode raw = (split raw).bind (fun words => words.mapM e.decode) := by
  cases hh : Encoding.unframe raw with
  | none => simp [Encoding.list, split, hh]
  | some hp =>
    rcases hp with ⟨header, payload⟩
    cases hw : Encoding.unframes (decodeNat header) payload with
    | none => simp [Encoding.list, Encoding.nat, split, hh, hw]
    | some wt =>
      rcases wt with ⟨words, tail⟩
      by_cases ht : tail = [] <;>
        simp [Encoding.list, Encoding.nat, split, hh, hw, ht]

private theorem unframe_raw {raw word tail : List Bool}
    (h : Encoding.unframe raw = some (word, tail)) : raw = Encoding.frame word ++ tail := by
  rw [Contract.unframe_eq] at h
  simpa only [Contract.frame_eq] using
    (GraphPreprocessing.Frame.unframe_some_iff raw word tail).mp h

/-- Raw frame parsing retains the exact word sequence and unconsumed suffix. -/
theorem unframes_some_iff (n : ℕ) (raw tail : List Bool) (words : List (List Bool)) :
    Encoding.unframes n raw = some (words, tail) ↔
      words.length = n ∧ raw = Encoding.frames words ++ tail := by
  constructor
  · intro h
    induction n generalizing raw words with
    | zero =>
      simp only [Encoding.unframes, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp [Encoding.frames]
    | succ n ih =>
      cases hu : Encoding.unframe raw with
      | none => simp [Encoding.unframes, hu] at h
      | some wt =>
        rcases wt with ⟨word, rest⟩
        cases hs : Encoding.unframes n rest with
        | none => simp [Encoding.unframes, hu, hs] at h
        | some wt =>
          rcases wt with ⟨more, suffix⟩
          simp [Encoding.unframes, hu, hs] at h
          rcases h with ⟨rfl, rfl⟩
          obtain ⟨hl, hr⟩ := ih rest more hs
          refine ⟨by simp [hl], ?_⟩
          rw [unframe_raw hu, hr]
          simp [Encoding.frames, List.append_assoc]
  · rintro ⟨rfl, rfl⟩
    exact Encoding.unframes_frames_append words tail

/-- All accepted raw representations, with no canonical-header restriction. -/
theorem split_some_iff (raw : List Bool) (words : List (List Bool)) :
    split raw = some words ↔ ∃ header : List Bool,
      decodeNat header = words.length ∧ raw = Encoding.frame header ++ Encoding.frames words := by
  constructor
  · intro h
    cases hh : Encoding.unframe raw with
    | none => simp [split, hh] at h
    | some hp =>
      rcases hp with ⟨header, payload⟩
      cases hw : Encoding.unframes (decodeNat header) payload with
      | none => simp [split, hh, hw] at h
      | some wt =>
        rcases wt with ⟨found, tail⟩
        by_cases ht : tail = []
        · subst tail
          simp [split, hh, hw] at h
          subst found
          obtain ⟨hc, hp⟩ := (unframes_some_iff _ _ _ _).mp hw
          exact ⟨header, hc.symm, by simpa only [List.append_nil] using (unframe_raw hh).trans (congrArg (Encoding.frame header ++ ·) hp)⟩
        · simp [split, hh, hw, ht] at h
  · rintro ⟨header, hc, rfl⟩
    simp [split, hc]

/-- An arbitrary accepted representation explicitly pays for every occurrence. -/
theorem split_size {raw : List Bool} {words : List (List Bool)} (h : split raw = some words) :
    words.length ≤ raw.length ∧ (words.map List.length).sum ≤ raw.length := by
  obtain ⟨header, _, rfl⟩ := (split_some_iff _ _).mp h
  simp only [List.length_append, Encoding.frame_length, Encoding.frames_length]
  omega

@[simp] theorem split_encode {α : Type} (e : Encoding.BitEncoding α) (xs : List α) :
    split ((Encoding.list e).encode xs) = some (xs.map e.encode) := by
  apply (split_some_iff _ _).mpr
  exact ⟨encodeNat xs.length, by simp, rfl⟩

/-- This stage retains the original header in its contract so the exact consumed
length is available, although its machine output is the canonical counter word. -/
structure Header where
  raw : List Bool
  payload : List Bool
  deriving DecidableEq

def header (raw : List Bool) : Option Header :=
  (Encoding.unframe raw).map (fun p => ⟨p.1, p.2⟩)

theorem header_some {raw : List Bool} {h : Header} (he : header raw = some h) :
    raw = Encoding.frame h.raw ++ h.payload := by
  cases hu : Encoding.unframe raw with
  | none => simp [header, hu] at he
  | some pair =>
    rcases pair with ⟨a, b⟩
    simp [header, hu] at he
    subst h
    exact unframe_raw hu

variable {K Λ τ : Type} [DecidableEq K]

/-- Raw source, extracted header, canonical counter, shared scratch. -/
abbrev Stacks (K : Type) := Fin 4 ↪ K

structure Labels (Λ : Type) where
  scan : Λ
  extract : Λ
  move : Λ
  highest : Λ
  restore : Λ
  next : Λ
  bad : Λ

def naturalStacks (st : Stacks K) : NaturalWords.Stacks K where
  toFun i := st ⟨i.val + 1, by omega⟩
  inj' := by intro i j h; have := st.injective h; apply Fin.ext; simpa using congrArg Fin.val this

def naturalLabels (lab : Labels Λ) : NaturalWords.Labels Λ :=
  ⟨lab.move, lab.highest, lab.restore, lab.next⟩

structure Executes (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (st : Stacks K) (lab : Labels Λ) : Prop where
  scan : ExecutesAt step lab.scan
    (GraphPreprocessing.Frame.scanStmt (st 0) (st 3) lab.scan lab.extract lab.bad)
  extract : ExecutesAt step lab.extract (copyMoveStmt (st 3) (st 1) lab.extract lab.move)
  natural : NaturalWords.Executes step (naturalStacks st) (naturalLabels lab)

def tapes (st : Stacks K) (frame : K → List Bool)
    (source rawHeader counter scratch : List Bool) : K → List Bool :=
  tapes3 (Function.update frame (st 2) counter) (st 0) (st 1) (st 3) source rawHeader scratch

@[simp] theorem tapes_at (st : Stacks K) (frame : K → List Bool)
    (source rawHeader counter scratch : List Bool) (i : Fin 4) :
    tapes st frame source rawHeader counter scratch (st i) =
      (![source, rawHeader, counter, scratch] : Fin 4 → List Bool) i := by
  fin_cases i <;> simp [tapes, tapes3, st.injective.eq_iff]

theorem tapes_other (st : Stacks K) (frame : K → List Bool)
    (source rawHeader counter scratch : List Bool) (k : K)
    (h : ∀ i : Fin 4, k ≠ st i) :
    tapes st frame source rawHeader counter scratch k = frame k := by
  simp [tapes, tapes3, h]

private theorem tapes_natural (st : Stacks K) (frame : K → List Bool)
    (source rawHeader counter scratch : List Bool) :
    tapes st frame source rawHeader counter scratch =
      NaturalWords.tapes (naturalStacks st) (Function.update frame (st 0) source)
        rawHeader counter scratch := by
  change tapes st frame source rawHeader counter scratch =
    tapes3 (Function.update frame (st 0) source) (st 1) (st 2) (st 3) rawHeader counter scratch
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    simp_all [tapes, NaturalWords.tapes, naturalStacks, tapes3, st.injective.eq_iff]

section Returning
variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (st : Stacks K) (lab : Labels Λ)
variable (exec : Executes step st lab) (memory : τ) (frame : K → List Bool)

include exec

/-- Actual framing followed immediately by exact raw-number canonicalization. -/
theorem header_exact (word payload : List Bool) :
    RunsExactly step
      (cfg lab.scan memory (tapes st frame (Encoding.frame word ++ payload) [] [] []))
      (cfg lab.next memory (tapes st frame payload [] (encodeNat (decodeNat word)) []))
      (4 * word.length + 5) := by
  have first : RunsExactly step
      (cfg lab.scan memory (tapes st frame (Encoding.frame word ++ payload) [] [] []))
      (cfg lab.move memory (tapes st frame payload word [] [])) (2 * (word.length + 1)) := by
    simpa only [tapes, Contract.frame_eq, List.append_nil] using
      GraphPreprocessing.Frame.extract_exact (st 0) (st 1) (st 3)
        (fun h => by have := st.injective h; contradiction)
        (fun h => by have := st.injective h; contradiction)
        (fun h => by have := st.injective h; contradiction)
        step lab.scan lab.extract lab.move lab.bad exec.scan exec.extract
        memory (Function.update frame (st 2) []) word payload []
  have second : RunsExactly step
      (cfg lab.move memory (tapes st frame payload word [] []))
      (cfg lab.next memory (tapes st frame payload [] (encodeNat (decodeNat word)) []))
      (2 * word.length + 3) := by
    simpa only [tapes_natural, naturalLabels, List.append_nil] using
      NaturalWords.canonicalize_exact step (naturalStacks st) (naturalLabels lab) exec.natural
        memory (Function.update frame (st 0) payload) word []
  convert first.trans second using 1 <;> omega

/-- Malformed framing also returns after a bit-bounded real execution. -/
theorem header_rejects (raw : List Bool) (h : Encoding.unframe raw = none) :
    ∃ (produced : List Bool) (time : ℕ), time ≤ raw.length + 1 ∧ produced.length ≤ raw.length ∧
      RunsExactly step (cfg lab.scan memory (tapes st frame raw [] [] []))
        (cfg lab.bad memory (tapes st frame [] [] [] produced.reverse)) time := by
  rw [Contract.unframe_eq] at h
  simpa only [tapes, List.append_nil] using
    GraphPreprocessing.Frame.rejects (st 0) (st 1) (st 3)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      step lab.scan lab.extract lab.bad exec.scan memory (Function.update frame (st 2) []) raw [] [] h

/-- All input words finish the header stage in a linear number of actual steps.
This has no dependence on the possibly exponentially large decoded count. -/
theorem header_terminates (raw : List Bool) :
    ∃ (ending : K → List Bool) (time : ℕ), time ≤ 2 * raw.length + 3 ∧
      RunsExactly step (cfg lab.scan memory (tapes st frame raw [] [] []))
        (cfg (if (header raw).isSome then lab.next else lab.bad) memory ending) time ∧
      (∀ k, (∀ i : Fin 4, k ≠ st i) → ending k = frame k) ∧
      (∀ h, header raw = some h → ending = tapes st frame h.payload [] (encodeNat (decodeNat h.raw)) []) := by
  cases hu : Encoding.unframe raw with
  | none =>
    obtain ⟨produced, time, ht, _, hr⟩ := header_rejects step st lab exec memory frame raw hu
    exact ⟨_, time, by omega, by simpa [header, hu] using hr,
      tapes_other st frame [] [] [] produced.reverse, by intro h hh; simp [header, hu] at hh⟩
  | some hp =>
    rcases hp with ⟨word, payload⟩
    have he := unframe_raw hu
    have hl := congrArg List.length he
    simp only [List.length_append, Encoding.frame_length] at hl
    refine ⟨_, 4 * word.length + 5, by omega, ?_,
      tapes_other st frame payload [] (encodeNat (decodeNat word)) [], ?_⟩
    · simpa [header, hu, he] using
        header_exact step st lab exec memory frame word payload
    · intro h hh
      simp [header, hu] at hh
      subst h
      rfl

end Returning

/-- Finite standalone client of the returning length-header protocol. -/
def localStacks : Stacks (Fin 4) := ⟨id, fun _ _ h => h⟩
def localLabels : Labels (Fin 7) := ⟨0, 1, 2, 3, 4, 5, 6⟩

def program (label : Fin 7) : Stmt (Fin 4) (Fin 7) Unit :=
  if label = 0 then GraphPreprocessing.Frame.scanStmt 0 3 0 1 6
  else if label = 1 then copyMoveStmt 3 1 1 2
  else if label = 2 then copyMoveStmt 1 3 2 3
  else if label = 3 then NaturalWords.highestStmt 3 2 4
  else if label = 4 then copyMoveStmt 3 2 4 5
  else halt

abbrev computer : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Fin 7
  main := 0
  σ := Option Bool × Unit
  initialState := (none, ())
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) :=
  inferInstanceAs (Fintype Bool)

theorem statement_budget (label : Fin 7) : TM2Cost.budget (program label) ≤ 8 := by
  fin_cases label <;> decide

theorem computer_executes : Executes computer.step localStacks localLabels := by
  constructor
  · intro state tape; rfl
  · intro state tape; rfl
  · constructor <;> intro state tape <;> rfl

theorem cfg_init (raw : List Bool) :
    cfg (0 : Fin 7) () (tapes localStacks (fun _ => []) raw [] [] []) = initList computer raw := by
  unfold cfg initList
  congr 1
  funext k
  fin_cases k <;> rfl

theorem computer_header (word payload : List Bool) :
    RunsExactly computer.step (initList computer (Encoding.frame word ++ payload))
      (cfg (5 : Fin 7) () (tapes localStacks (fun _ => []) payload [] (encodeNat (decodeNat word)) []))
      (4 * word.length + 5) := by
  simpa only [localLabels, cfg_init] using
    header_exact computer.step localStacks localLabels computer_executes () (fun _ => []) word payload

theorem computer_terminates (raw : List Bool) :
    ∃ (ending : Fin 4 → List Bool) (time : ℕ), time ≤ 2 * raw.length + 3 ∧
      RunsExactly computer.step (initList computer raw)
        (cfg (if (header raw).isSome then (5 : Fin 7) else 6) () ending) time := by
  obtain ⟨ending, time, ht, hr, _, _⟩ :=
    header_terminates computer.step localStacks localLabels computer_executes () (fun _ => []) raw
  exact ⟨ending, time, ht, by simpa only [localLabels, cfg_init] using hr⟩

theorem return_halts (good : Bool) (saved : Fin 4 → List Bool) :
    computer.step (cfg (if good then 5 else 6) () saved) =
      some (⟨none, (none, ()), saved⟩ : computer.Cfg) := by
  cases good <;> rfl

theorem computer_halts (raw : List Bool) :
    ∃ (saved : Fin 4 → List Bool) (time : ℕ), time ≤ 2 * raw.length + 4 ∧
      RunsExactly computer.step (initList computer raw)
        (⟨none, (none, ()), saved⟩ : computer.Cfg) time := by
  obtain ⟨saved, time, ht, hr⟩ := computer_terminates raw
  exact ⟨saved, 1 + time, by omega,
    hr.trans (runsExactly_one (return_halts (header raw).isSome saved))⟩

end Counting.Algorithm.KarpLubyRequest.ListFields
