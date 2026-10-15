import Counting.Algorithm.KarpLubyRequest.Verifier

/-!
# Compilation of an actual element verifier into a list verifier

The finite caller first validates the raw length header and framing through
`CountedList`, then extracts and calls the source program once per physical
payload. H1's returning compiler inlines the source instructions. Neither the
semantic predicate nor a natural-number loop appears in finite control.
-/
namespace Counting.Algorithm.KarpLubyRequest.ListVerifier
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby

variable {K Λ : Type} [DecidableEq K]
variable (v : Verifier K Λ)

abbrev Stack (K : Type) := K ⊕ Fin 3
abbrev Label (Λ : Type) := Λ ⊕ Fin 17

def stackMap : CountedList.Full.Stacks (Stack K) :=
  ⟨fun i => ![Sum.inl v.input, Sum.inr 0, Sum.inr 1, Sum.inr 2] i, by
    intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

@[simp] theorem stackMap_zero : stackMap v 0 = Sum.inl v.input := rfl
@[simp] theorem stackMap_one : stackMap v 1 = Sum.inr 0 := rfl
@[simp] theorem stackMap_two : stackMap v 2 = Sum.inr 1 := rfl
@[simp] theorem stackMap_three : stackMap v 3 = Sum.inr 2 := rfl

def labels : CountedList.Full.Labels (Label Λ) :=
  ⟨.inr 0, .inr 1, .inr 2, .inr 3, .inr 4, .inr 5, .inr 6,
    .inr 7, .inr 8, .inr 9, .inr 10, .inr 11, .inr 16⟩

def loopStmt : Stmt (Stack K) (Label Λ) Bool :=
  .peek (.inr 0) (fun s b => (b, s.2))
    (.branch (fun s => s.1.isSome)
      (.load (fun _ => (none, false)) (.goto (fun _ => .inr 12)))
      (.load (fun _ => (none, false)) (.goto (fun _ => .inr 15))))

def outside (label : Fin 17) : Stmt (Stack K) (Label Λ) Bool :=
  if label = 0 then Frame.scanStmt (.inl v.input) (.inr 2) (.inr 0) (.inr 1) (.inr 16)
  else if label = 1 then copyMoveStmt (.inr 2) (.inr 0) (.inr 1) (.inr 2)
  else if label = 2 then copyMoveStmt (.inr 0) (.inr 2) (.inr 2) (.inr 3)
  else if label = 3 then NaturalWords.highestStmt (.inr 2) (.inr 1) (.inr 4)
  else if label = 4 then copyMoveStmt (.inr 2) (.inr 1) (.inr 4) (.inr 5)
  else if label = 5 then copyMoveStmt (.inl v.input) (.inr 2) (.inr 5) (.inr 6)
  else if label = 6 then copyRestoreStmt (.inl v.input) (.inr 0) (.inr 2) (.inr 6) (.inr 7)
  else if label = 7 then CountedList.Body.checkStmt (.inl v.input) (.inr 1) (.inr 8) (.inr 11) (.inr 16)
  else if label = 8 then ListScan.skipStmt (.inl v.input) (.inr 8) (.inr 9) (.inr 16)
  else if label = 9 then CountedList.Counter.decrementStmt (.inr 1) (.inr 2) (.inr 9) (.inr 10)
  else if label = 10 then copyMoveStmt (.inr 2) (.inr 1) (.inr 10) (.inr 7)
  else if label = 11 then loopStmt
  else if label = 12 then Frame.scanStmt (.inr 0) (.inr 2) (.inr 12) (.inr 13) (.inr 16)
  else if label = 13 then copyMoveStmt (.inr 2) (.inl v.input) (.inr 13) (.inl v.main)
  else if label = 14 then .branch (fun s => s.2)
    (.load (fun _ => (none, false)) (.goto (fun _ => .inr 11)))
    (.load (fun _ => (none, false)) (.goto (fun _ => .inr 16)))
  else if label = 15 then .load (fun _ => (none, true)) .halt
  else .load (fun _ => (none, false)) .halt

/-- The complete source finite program is inlined at every source label. -/
def program : Label Λ → Stmt (Stack K) (Label Λ) Bool :=
  Returning.program (14 : Fin 17) v.program (outside v)

def tapes (raw frames counter scratch original : List Bool) : Stack K → List Bool :=
  Sum.elim (verifierTapes v.input v.ambient raw original) ![frames, counter, scratch]

@[simp] theorem tapes_inl (raw frames counter scratch original : List Bool) (k : K) :
    tapes v raw frames counter scratch original (.inl k) =
      verifierTapes v.input v.ambient raw original k := rfl

private theorem as_list (raw frames counter scratch original : List Bool) :
    tapes v raw frames counter scratch original = CountedList.Full.tapes (stackMap v)
      (tapes v [] [] [] [] original) raw frames counter scratch := by
  have hne := v.distinct
  funext k
  simp only [tapes, CountedList.Full.tapes, ListFields.tapes, tapes3]
  simp only [Function.update_apply]
  cases k with
  | inl k => by_cases hi : k = v.input <;> by_cases ha : k = v.ambient <;>
      simp_all [verifierTapes, Function.update_apply]
  | inr k => fin_cases k <;> simp

private theorem as_frame (raw frames scratch original : List Bool) :
    tapes v raw frames [] scratch original = tapes3 (tapes v [] [] [] [] original)
      (.inr 0) (.inl v.input) (.inr 2) frames raw scratch := by
  have hne := v.distinct
  funext k
  simp only [tapes, tapes3]
  simp only [Function.update_apply]
  cases k with
  | inl k => by_cases hi : k = v.input <;> by_cases ha : k = v.ambient <;>
      simp_all [verifierTapes, Function.update_apply]
  | inr k => fin_cases k <;> simp

@[simp] theorem tapes_initial (raw original : List Bool) :
    tapes v raw [] [] [] original =
      verifierTapes (Sum.inl v.input : Stack K) (.inl v.ambient) raw original := by
  funext k
  cases k with
  | inl k => simp [tapes, -Sum.elim_update_left, -Sum.update_elim_inl, verifierTapes, Function.comp_def]
  | inr k => fin_cases k <;> simp [tapes, -Sum.elim_update_left, -Sum.update_elim_inl, verifierTapes, Function.comp_def]

theorem list_executes : CountedList.Full.Executes (TM2.step (program v)) (stackMap v) labels := by
  constructor
  · constructor
    · intro state stk; rfl
    · intro state stk; rfl
    · constructor <;> intro state stk <;> rfl
  · constructor <;> intro state stk <;> rfl

theorem frame_exact (word rest original : List Bool) :
    RunsExactly (TM2.step (program v))
      (cfg (.inr 12) false (tapes v [] (Encoding.frame word ++ rest) [] [] original))
      (cfg (.inl v.main) false (tapes v word rest [] [] original)) (2 * (word.length + 1)) := by
  simpa only [← as_frame, Contract.frame_eq, List.append_nil] using
    Frame.extract_exact (Sum.inr 0 : Stack K) (.inl v.input) (.inr 2)
      (by simp) (by simp) (by simp)
      (TM2.step (program v)) (.inr 12) (.inr 13) (.inl v.main) (.inr 16)
      (by intro state stk; rfl) (by intro state stk; rfl) false
      (tapes v [] [] [] [] original) word rest []

theorem source_run (raw rest original : List Bool) :
    ∃ ending time, time ≤ v.bound raw.length original.length ∧
      RunsExactly (TM2.step (program v))
        (cfg (.inl v.main) false (tapes v raw rest [] [] original))
        (cfg (.inr 14) (v.accepts raw original) (Sum.elim ending ![rest, [], []])) time ∧
      (v.accepts raw original = true → ending = verifierTapes v.input v.ambient [] original) := by
  obtain ⟨ending, time, ht, hr, hs⟩ := v.run raw original
  have lift := Returning.run_program (14 : Fin 17) v.program (outside v)
    (cfg v.main false (verifierTapes v.input v.ambient raw original))
    (⟨none, (none, v.accepts raw original), ending⟩ : Cfg K Λ Bool)
    ![rest, [], []] time hr
  exact ⟨ending, time, ht, lift, hs⟩

private theorem loop_nil (original : List Bool) :
    TM2.step (program v) (cfg (.inr 11) false (tapes v [] [] [] [] original)) =
      some (cfg (.inr 15) false (tapes v [] [] [] [] original)) := rfl

private theorem loop_cons (word rest original : List Bool) :
    TM2.step (program v) (cfg (.inr 11) false
      (tapes v [] (Encoding.frame word ++ rest) [] [] original)) =
      some (cfg (.inr 12) false (tapes v [] (Encoding.frame word ++ rest) [] [] original)) := by
  cases word <;> rfl

private theorem dispatch (good : Bool) (ending : Stack K → List Bool) :
    TM2.step (program v) (cfg (.inr 14) good ending) =
      some (cfg (if good then .inr 11 else .inr 16) false ending) := by
  cases good <;> rfl

/-- Physical per-element accounting includes the source call, extraction, and
both loop/return dispatches. -/
def scanBound (words : List (List Bool)) (ambientLength : ℕ) : ℕ :=
  (words.map (fun word => v.bound word.length ambientLength + 2 * word.length + 4)).sum + 1

theorem scan_run (words : List (List Bool)) (original : List Bool) :
    ∃ ending time, time ≤ scanBound v words original.length ∧
      RunsExactly (TM2.step (program v))
        (cfg (.inr 11) false (tapes v [] (Encoding.frames words) [] [] original))
        (cfg (if words.all (fun word => v.accepts word original) then .inr 15 else .inr 16)
          false ending) time ∧
      (words.all (fun word => v.accepts word original) = true →
        ending = tapes v [] [] [] [] original) := by
  induction words with
  | nil => exact ⟨_, 1, by simp [scanBound], runsExactly_one (loop_nil v original), by simp⟩
  | cons word words ih =>
    have r1 := runsExactly_one (loop_cons v word (Encoding.frames words) original)
    have r2 := frame_exact v word (Encoding.frames words) original
    obtain ⟨saved, time, ht, hr, hs⟩ := source_run v word (Encoding.frames words) original
    have r3 := runsExactly_one (dispatch v (v.accepts word original)
      (Sum.elim saved ![Encoding.frames words, [], []]))
    cases hc : v.accepts word original with
    | false =>
      refine ⟨Sum.elim saved ![Encoding.frames words, [], []], 1 + (time + (2 * (word.length + 1) + 1)), ?_, ?_, by simp [hc]⟩
      · simp only [scanBound, List.map_cons, List.sum_cons]; omega
      · simpa only [hc, List.all_cons, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          Encoding.frames] using ((r1.trans r2).trans hr).trans r3
    | true =>
      have he := hs hc
      subst saved
      have r : RunsExactly (TM2.step (program v))
          (cfg (.inr 11) false (tapes v [] (Encoding.frames (word :: words)) [] [] original))
          (cfg (.inr 11) false (tapes v [] (Encoding.frames words) [] [] original))
          (1 + (time + (2 * (word.length + 1) + 1))) := by
        simpa only [hc, ↓reduceIte, Encoding.frames, tapes] using ((r1.trans r2).trans hr).trans r3
      obtain ⟨ending, more, hm, rr, hh⟩ := ih
      refine ⟨ending, more + (1 + (time + (2 * (word.length + 1) + 1))), ?_, ?_, ?_⟩
      · simp only [scanBound, List.map_cons, List.sum_cons] at *; omega
      · simpa only [List.all_cons, hc, Bool.true_and] using r.trans rr
      · simpa only [List.all_cons, hc, Bool.true_and] using hh

def accepts (raw original : List Bool) : Bool :=
  match ListFields.split raw with
  | none => false
  | some words => words.all (fun word => v.accepts word original)

/-- Polynomial substitution on the source bound, with occurrence count charged
by actual encoded input length. -/
def bound (m n : ℕ) : ℕ :=
  CountedList.Full.timeBound m + m * (v.bound m n + 2 * m + 4) + 2

theorem scanBound_le (words : List (List Bool)) (m n : ℕ)
    (h : ∀ word ∈ words, word.length ≤ m) :
    scanBound v words n ≤ words.length * (v.bound m n + 2 * m + 4) + 1 := by
  unfold scanBound
  suffices (words.map (fun word => v.bound word.length n + 2 * word.length + 4)).sum ≤
      words.length * (v.bound m n + 2 * m + 4) by omega
  induction words with
  | nil => simp
  | cons word words ih =>
    have hw := h word (by simp)
    have hi := ih (fun w hh => h w (by simp [hh]))
    have hv := v.monotone hw (le_refl n)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul]
    omega

theorem return_halts (good : Bool) (ending : Stack K → List Bool) :
    TM2.step (program v) (cfg (if good then .inr 15 else .inr 16) false ending) =
      some (⟨none, (none, good), ending⟩ : Cfg (Stack K) (Label Λ) Bool) := by
  cases good <;> rfl

theorem run (raw original : List Bool) :
    ∃ ending time, time ≤ bound v raw.length original.length ∧
      RunsExactly (TM2.step (program v))
        (cfg (.inr 0) false (verifierTapes (Sum.inl v.input : Stack K) (.inl v.ambient) raw original))
        (⟨none, (none, accepts v raw original), ending⟩ : Cfg (Stack K) (Label Λ) Bool) time ∧
      (accepts v raw original = true →
        ending = verifierTapes (Sum.inl v.input : Stack K) (.inl v.ambient) [] original) := by
  obtain ⟨saved, time, ht, hr, _, hs⟩ := CountedList.Full.terminates (TM2.step (program v))
    (stackMap v) labels (list_executes v) false (tapes v [] [] [] [] original) raw
  have hr' : RunsExactly (TM2.step (program v))
      (cfg (.inr 0) false (tapes v raw [] [] [] original))
      (cfg (if (ListFields.split raw).isSome then .inr 11 else .inr 16) false saved) time := by
    simpa only [← as_list, labels] using hr
  cases hp : ListFields.split raw with
  | none =>
    simp only [hp, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hr'
    refine ⟨saved, 1 + time, by unfold bound; omega, ?_, by simp [accepts, hp]⟩
    simpa only [tapes_initial, accepts, hp] using
      hr'.trans (runsExactly_one (return_halts v false saved))
  | some words =>
    have he : saved = tapes v [] (Encoding.frames words) [] [] original := by
      simpa only [← as_list] using hs words hp
    simp only [hp, Option.isSome_some, ↓reduceIte, he] at hr'
    obtain ⟨ending, more, hm, rr, hh⟩ := scan_run v words original
    have final := runsExactly_one (return_halts v (words.all (fun word => v.accepts word original)) ending)
    refine ⟨ending, 1 + (more + time), ?_, ?_, ?_⟩
    · obtain ⟨hc, hl⟩ := ListFields.split_size hp
      have hw : ∀ word ∈ words, word.length ≤ raw.length := by
        intro word hw
        have hs : word.length ≤ (words.map List.length).sum :=
          List.single_le_sum (fun x hx => Nat.zero_le x) _ (List.mem_map_of_mem hw)
        omega
      have hb := scanBound_le v words raw.length original.length hw
      have hm' := Nat.mul_le_mul_right (v.bound raw.length original.length + 2 * raw.length + 4) hc
      unfold bound; omega
    · simpa only [tapes_initial, accepts, hp] using (hr'.trans rr).trans final
    · simpa only [accepts, hp, tapes_initial] using hh

theorem bound_mono {m n x y : ℕ} (hm : m ≤ n) (hx : x ≤ y) :
    bound v m x ≤ bound v n y := by
  have hv := v.monotone hm hx
  have hp := Nat.mul_le_mul hm (by omega : v.bound m x + 2 * m + 4 ≤ v.bound n y + 2 * n + 4)
  have hq := Nat.mul_le_mul (by omega : m + 1 ≤ n + 1) (by omega : 2 * m + 12 ≤ 2 * n + 12)
  unfold bound CountedList.Full.timeBound
  omega

theorem statement_budget (label : Label Λ) : TM2Cost.budget (program v label) ≤ max v.budget 8 := by
  cases label with
  | inl label =>
    simpa only [program, Returning.program, Returning.budget_block] using
      (v.statement_budget label).trans (Nat.le_max_left v.budget 8)
  | inr label =>
    have h : TM2Cost.budget (outside v label) ≤ 8 := by
      fin_cases label <;>
        simp [outside, loopStmt, TM2Cost.budget, Frame.scanStmt, copyMoveStmt, copyRestoreStmt,
          NaturalWords.highestStmt, CountedList.Body.checkStmt, ListScan.skipStmt,
          CountedList.Counter.decrementStmt]
    exact h.trans (Nat.le_max_right _ _)

/-- Applying this compiler twice invokes the same physical traversal at both
DNF list levels. Its source is a concrete finite program with a proven run. -/
def compile : Verifier (Stack K) (Label Λ) where
  input := .inl v.input
  ambient := .inl v.ambient
  distinct := by simpa using v.distinct
  main := .inr 0
  program := program v
  accepts := accepts v
  bound := bound v
  monotone := bound_mono v
  budget := max v.budget 8
  statement_budget := statement_budget v
  run := run v

end Counting.Algorithm.KarpLubyRequest.ListVerifier
