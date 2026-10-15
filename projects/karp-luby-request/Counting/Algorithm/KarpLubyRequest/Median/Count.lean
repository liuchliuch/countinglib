import Counting.Algorithm.KarpLubyRequest.Median.Routines
import Counting.Algorithm.KarpLubyRequest.Median.Semantics

/-! Actual inner scanning, occurrence counting, and strict-majority cancellation. -/
namespace Counting.Algorithm.KarpLubyRequest.Median.Program
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby

/-- Proof-side description of stack contents, never a machine register. -/
def bank (input saved inner candidate chosen : List Bool) (lo hi : ℕ) : Stack → List Bool
  | .input => input | .saved => saved | .inner => inner | .candidate => candidate | .chosen => chosen
  | .below => List.replicate lo true | .above => List.replicate hi true
  | _ => []

def words (xs : List ℕ) : List Bool := Encoding.frames (xs.map encodeNat)
@[simp] theorem words_nil : words [] = [] := rfl
@[simp] theorem words_cons (a : ℕ) (xs : List ℕ) :
    words (a :: xs) = Encoding.frame (encodeNat a) ++ words xs := rfl
theorem words_cons_ne_nil (a : ℕ) (xs : List ℕ) : words (a :: xs) ≠ [] := by
  rw [words_cons]
  intro h
  have hl := congrArg List.length h
  simp only [List.length_append, Encoding.frame_length, List.length_nil] at hl
  omega

/-- A bound carries an actual number of TM2 transitions as its witness. -/
def Run (a b : Cfg Stack Label Memory) (bound : ℕ) : Prop :=
  ∃ time, time ≤ bound ∧ RunsExactly computer.step a b time

theorem Run.exact {a b : Cfg Stack Label Memory} {n : ℕ}
    (h : RunsExactly computer.step a b n) : Run a b n := ⟨n, le_rfl, h⟩
theorem Run.mono {a b : Cfg Stack Label Memory} {n m : ℕ}
    (h : Run a b n) (hn : n ≤ m) : Run a b m := by
  obtain ⟨t, ht, hr⟩ := h; exact ⟨t, ht.trans hn, hr⟩
theorem Run.trans {a b c : Cfg Stack Label Memory} {n m : ℕ}
    (h : Run a b n) (h' : Run b c m) : Run a c (n + m) := by
  obtain ⟨t, ht, hr⟩ := h
  obtain ⟨u, hu, hs⟩ := h'
  exact ⟨u + t, by omega, hr.trans hs⟩
theorem Run.one {a b : Cfg Stack Label Memory} (h : computer.step a = some b) : Run a b 1 :=
  Run.exact (runsExactly_one h)

theorem inner_nonempty (m : Memory) (t : Stack → List Bool) (h : t .inner ≠ []) :
    Run (cfg .inner m t) (cfg (.scan .member) m t) 1 := by
  apply Run.one
  change TM2.step program _ = _
  cases hx : t .inner with
  | nil => exact False.elim (h hx)
  | cons b bs => simp [TM2.step, program, TM2.stepAux, cfg, hx]

theorem inner_empty (m : Memory) (t : Stack → List Bool) (h : t .inner = []) :
    Run (cfg .inner m t) (cfg .balance m t) 1 := by
  apply Run.one
  change TM2.step program _ = _
  simp [TM2.step, program, TM2.stepAux, cfg, h]

theorem member_run (selected eligible : Bool) (input saved tail chosen : List Bool)
    (a b lo hi : ℕ) :
    Run
      (cfg (.scan .member) (memory selected eligible)
        (bank input saved (Encoding.frame (encodeNat b) ++ tail) (encodeNat a) chosen lo hi))
      (cfg .inner (memory selected eligible)
        (bank input saved tail (encodeNat a) chosen
          (lo + if b ≤ a then 1 else 0) (hi + if a < b then 1 else 0)))
      (2 * (encodeNat b).length + 2 * (encodeNat a).length +
        max (encodeNat a).length (encodeNat b).length + 6) := by
  let base := bank input saved tail (encodeNat a) chosen lo hi
  have h₁ := frame_run .member (memory selected eligible)
    (bank input saved (Encoding.frame (encodeNat b) ++ tail) (encodeNat a) chosen lo hi)
    (encodeNat b) tail rfl rfl rfl
  have e₁ : Function.update (Function.update
      (bank input saved (Encoding.frame (encodeNat b) ++ tail) (encodeNat a) chosen lo hi)
        (frameSrc .member) tail) (frameDst .member) (encodeNat b) =
      comparisonTapes base [] (encodeNat b) [] := by funext k; cases k <;> rfl
  rw [e₁] at h₁
  have h₂ := copy_run .countLeft (memory selected eligible)
    (comparisonTapes base [] (encodeNat b) []) rfl rfl
  have e₂ : Function.update (comparisonTapes base [] (encodeNat b) []) (copyDst .countLeft)
      ((comparisonTapes base [] (encodeNat b) []) (copySrc .countLeft)) =
      comparisonTapes base (encodeNat a) (encodeNat b) [] := by funext k; cases k <;> rfl
  rw [e₂] at h₂
  have h₃ := comparison_run false selected eligible base a b
  have h₄ : Run
      (cfg .mark (memory selected eligible) (comparisonTapes base [] [] [decide (a < b)]))
      (cfg .inner (memory selected eligible)
        (bank input saved tail (encodeNat a) chosen
          (lo + if b ≤ a then 1 else 0) (hi + if a < b then 1 else 0))) 1 := by
    apply Run.one
    change TM2.step program _ = _
    by_cases h : a < b
    · have hn : ¬ b ≤ a := by omega
      simp only [h, hn, decide_true, ite_false, ite_true, Nat.add_zero]
      simp [TM2.step, program, TM2.stepAux, cfg, comparisonTapes, memory, base, bank, Function.update_apply]
      congr 2
      funext k; cases k <;> simp [Function.update_apply, bank, List.replicate_succ]
    · have hn : b ≤ a := by omega
      simp only [h, hn, decide_false, ite_false, ite_true, Nat.add_zero]
      simp [TM2.step, program, TM2.stepAux, cfg, comparisonTapes, memory, base, bank, Function.update_apply]
      congr 2
      funext k; cases k <;> simp [Function.update_apply, bank, List.replicate_succ]
  have run := ((Run.exact h₁).trans (Run.exact h₂)).trans ((Run.exact h₃).trans h₄)
  exact run.mono (by simp [comparisonTapes, base, bank, copySrc]; omega)

theorem count_run (xs : List ℕ) (selected eligible : Bool)
    (input saved chosen : List Bool) (a lo hi W : ℕ)
    (ha : (encodeNat a).length ≤ W) (hx : ∀ b ∈ xs, (encodeNat b).length ≤ W) :
    Run (cfg .inner (memory selected eligible)
        (bank input saved (words xs) (encodeNat a) chosen lo hi))
      (cfg .balance (memory selected eligible)
        (bank input saved [] (encodeNat a) chosen (lo + below xs a) (hi + above xs a)))
      (xs.length * (5 * W + 7) + 1) := by
  induction xs generalizing lo hi with
  | nil =>
    simpa using inner_empty (memory selected eligible)
      (bank input saved [] (encodeNat a) chosen lo hi) rfl
  | cons b bs ih =>
    have hb := hx b (by simp)
    have hbs : ∀ c ∈ bs, (encodeNat c).length ≤ W := fun c hc => hx c (by simp [hc])
    have h₀ := inner_nonempty (memory selected eligible)
      (bank input saved (words (b :: bs)) (encodeNat a) chosen lo hi) (words_cons_ne_nil b bs)
    have h₁ := member_run selected eligible input saved (words bs) chosen a b lo hi
    have h₂ := ih (lo + if b ≤ a then 1 else 0) (hi + if a < b then 1 else 0) hbs
    have run := (h₀.trans h₁).trans h₂
    have e₁ : lo + (if b ≤ a then 1 else 0) + below bs a = lo + below (b :: bs) a := by
      rw [below_cons]; omega
    have e₂ : hi + (if a < b then 1 else 0) + above bs a = hi + above (b :: bs) a := by
      rw [above_cons]; omega
    rw [e₁, e₂] at run
    exact run.mono (by simp only [List.length_cons]; have hm := max_le ha hb; nlinarith)

theorem balance_run (selected previous : Bool) (input saved chosen candidate : List Bool) (lo hi : ℕ) :
    Run (cfg .balance (memory selected previous) (bank input saved [] candidate chosen lo hi))
      (cfg .choose (memory selected (decide (hi < lo))) (bank input saved [] candidate chosen 0 0))
      (lo + hi + 3) := by
  induction lo generalizing hi with
  | zero =>
    have h₀ : Run (cfg .balance (memory selected previous) (bank input saved [] candidate chosen 0 hi))
        (cfg (.clear .below) (memory selected false) (bank input saved [] candidate chosen 0 hi)) 1 := by
      apply Run.one
      change TM2.step program _ = _
      simp [TM2.step, program, TM2.stepAux, cfg, memory, bank]
    have h₁ := clear_run .below (memory selected false) (bank input saved [] candidate chosen 0 hi)
    have e₁ : Function.update (bank input saved [] candidate chosen 0 hi) (clearStack .below) [] =
        bank input saved [] candidate chosen 0 hi := by funext k; cases k <;> rfl
    rw [e₁] at h₁
    have h₂ := clear_run .above (memory selected false) (bank input saved [] candidate chosen 0 hi)
    have e₂ : Function.update (bank input saved [] candidate chosen 0 hi) (clearStack .above) [] =
        bank input saved [] candidate chosen 0 0 := by funext k; cases k <;> rfl
    rw [e₂] at h₂
    have run := (h₀.trans (Run.exact h₁)).trans (Run.exact h₂)
    simpa [bank, clearStack, clearNext, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run
  | succ lo ih =>
    cases hi with
    | zero =>
      have h₀ : Run
          (cfg .balance (memory selected previous) (bank input saved [] candidate chosen (lo + 1) 0))
          (cfg (.clear .below) (memory selected true) (bank input saved [] candidate chosen lo 0)) 1 := by
        apply Run.one
        change TM2.step program _ = _
        simp [TM2.step, program, TM2.stepAux, cfg, memory, bank, List.replicate_succ, Function.update_apply]
        congr 2
        funext k; cases k <;> simp [Function.update_apply, bank, List.replicate_succ]
      have h₁ := clear_run .below (memory selected true) (bank input saved [] candidate chosen lo 0)
      have e₁ : Function.update (bank input saved [] candidate chosen lo 0) (clearStack .below) [] =
          bank input saved [] candidate chosen 0 0 := by funext k; cases k <;> rfl
      rw [e₁] at h₁
      have h₂ := clear_run .above (memory selected true) (bank input saved [] candidate chosen 0 0)
      have e₂ : Function.update (bank input saved [] candidate chosen 0 0) (clearStack .above) [] =
          bank input saved [] candidate chosen 0 0 := by funext k; cases k <;> rfl
      rw [e₂] at h₂
      have run := (h₀.trans (Run.exact h₁)).trans (Run.exact h₂)
      simp only [Nat.zero_lt_succ, decide_true]
      exact run.mono (by simp [bank, clearStack]; omega)
    | succ hi =>
      have h₀ : Run
          (cfg .balance (memory selected previous) (bank input saved [] candidate chosen (lo + 1) (hi + 1)))
          (cfg .balance (memory selected previous) (bank input saved [] candidate chosen lo hi)) 1 := by
        apply Run.one
        change TM2.step program _ = _
        simp [TM2.step, program, TM2.stepAux, cfg, memory, bank, List.replicate_succ, Function.update_apply]
        congr 2
        funext k; cases k <;> simp [Function.update_apply, bank, List.replicate_succ]
      have run := h₀.trans (ih hi)
      simpa only [Nat.succ_lt_succ_iff] using run.mono (by omega)

/-- Both physical token stacks have been cleared on return. -/
theorem eligibility_run (xs : List ℕ) (selected previous : Bool)
    (input saved chosen : List Bool) (a W : ℕ)
    (ha : (encodeNat a).length ≤ W) (hx : ∀ b ∈ xs, (encodeNat b).length ≤ W) :
    Run (cfg .inner (memory selected previous)
        (bank input saved (words xs) (encodeNat a) chosen 0 0))
      (cfg .choose (memory selected (eligible xs a))
        (bank input saved [] (encodeNat a) chosen 0 0))
      (xs.length * (5 * W + 8) + 4) := by
  have h₁ := count_run xs selected previous input saved chosen a 0 0 W ha hx
  simp only [Nat.zero_add] at h₁
  have h₂ := balance_run selected previous input saved chosen (encodeNat a) (below xs a) (above xs a)
  have run := h₁.trans h₂
  exact run.mono (by rw [count_partition]; nlinarith)

end Counting.Algorithm.KarpLubyRequest.Median.Program
