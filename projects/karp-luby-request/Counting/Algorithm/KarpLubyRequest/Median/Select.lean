import Counting.Algorithm.KarpLubyRequest.Median.Count

/-! Actual retained-minimum updates and the outer candidate loop. -/
namespace Counting.Algorithm.KarpLubyRequest.Median.Program
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby

def ChosenBound (q : Option ℕ) (W : ℕ) : Prop := ∀ b, q = some b → (encodeNat b).length ≤ W

theorem insert_bound (q : Option ℕ) (a W : ℕ) (hq : ChosenBound q W)
    (ha : (encodeNat a).length ≤ W) : ChosenBound (insert q a) W := by
  intro b hb
  cases q with
  | none =>
    simp only [insert, Option.some.injEq] at hb
    simpa only [hb] using ha
  | some c =>
    by_cases h : a < c
    · simp only [insert, h, ite_true, Option.some.injEq] at hb
      simpa only [hb] using ha
    · simp only [insert, h, ite_false, Option.some.injEq] at hb
      subst b; exact hq c rfl

theorem candidate_clear (selected eligible : Bool) (input saved candidate chosen : List Bool) :
    Run (cfg (.clear .candidate) (memory selected eligible) (bank input saved [] candidate chosen 0 0))
      (cfg .outer (memory selected eligible) (bank input saved [] [] chosen 0 0))
      (candidate.length + 1) := by
  have h := clear_run .candidate (memory selected eligible) (bank input saved [] candidate chosen 0 0)
  have e : Function.update (bank input saved [] candidate chosen 0 0) (clearStack .candidate) [] =
      bank input saved [] [] chosen 0 0 := by funext k; cases k <;> rfl
  rw [e] at h
  simpa only [clearNext, clearStack, bank] using Run.exact h

theorem record_run (selected eligible : Bool) (input saved candidate : List Bool) :
    Run (cfg (.copyMove .chosen) (memory selected eligible) (bank input saved [] candidate [] 0 0))
      (cfg .outer (memory true eligible) (bank input saved [] [] candidate 0 0))
      (3 * candidate.length + 4) := by
  have h₁ := copy_run .chosen (memory selected eligible) (bank input saved [] candidate [] 0 0) rfl rfl
  have e : Function.update (bank input saved [] candidate [] 0 0) (copyDst .chosen)
      ((bank input saved [] candidate [] 0 0) (copySrc .chosen)) =
      bank input saved [] candidate candidate 0 0 := by funext k; cases k <;> rfl
  rw [e] at h₁
  have h₂ : Run (cfg .record (memory selected eligible) (bank input saved [] candidate candidate 0 0))
      (cfg (.clear .candidate) (memory true eligible) (bank input saved [] candidate candidate 0 0)) 1 :=
    Run.one rfl
  have h₃ := candidate_clear true eligible input saved candidate candidate
  exact ((Run.exact h₁).trans (h₂.trans h₃)).mono (by dsimp [bank, copySrc]; omega)

theorem replace_run (selected eligible : Bool) (input saved candidate chosen : List Bool) :
    Run (cfg (.clear .chosen) (memory selected eligible) (bank input saved [] candidate chosen 0 0))
      (cfg .outer (memory true eligible) (bank input saved [] [] candidate 0 0))
      (3 * candidate.length + chosen.length + 5) := by
  have h₁ := clear_run .chosen (memory selected eligible) (bank input saved [] candidate chosen 0 0)
  have e : Function.update (bank input saved [] candidate chosen 0 0) (clearStack .chosen) [] =
      bank input saved [] candidate [] 0 0 := by funext k; cases k <;> rfl
  rw [e] at h₁
  have h₂ := record_run selected eligible input saved candidate
  exact ((Run.exact h₁).trans h₂).mono (by dsimp [bank, clearStack]; omega)

theorem minimum_run (input saved : List Bool) (a b W : ℕ)
    (ha : (encodeNat a).length ≤ W) (hb : (encodeNat b).length ≤ W) :
    Run (cfg (.copyMove .minLeft) (memory true true)
        (bank input saved [] (encodeNat a) (encodeNat b) 0 0))
      (cfg .outer (memory true true)
        (bank input saved [] [] (encodeNat (if a < b then a else b)) 0 0))
      (10 * W + 19) := by
  let base := bank input saved [] (encodeNat a) (encodeNat b) 0 0
  have h₁ := copy_run .minLeft (memory true true) base rfl rfl
  have e₁ : Function.update base (copyDst .minLeft) (base (copySrc .minLeft)) =
      comparisonTapes base (encodeNat a) [] [] := by funext k; cases k <;> rfl
  rw [e₁] at h₁
  have h₂ := copy_run .minRight (memory true true) (comparisonTapes base (encodeNat a) [] []) rfl rfl
  have e₂ : Function.update (comparisonTapes base (encodeNat a) [] []) (copyDst .minRight)
      ((comparisonTapes base (encodeNat a) [] []) (copySrc .minRight)) =
      comparisonTapes base (encodeNat a) (encodeNat b) [] := by funext k; cases k <;> rfl
  rw [e₂] at h₂
  have h₃ := comparison_run true true true base a b
  have h₄ : Run (cfg .minimum (memory true true) (comparisonTapes base [] [] [decide (a < b)]))
      (cfg (if a < b then .clear .chosen else .clear .candidate) (memory true true) base) 1 := by
    apply Run.one
    change TM2.step program _ = _
    by_cases h : a < b <;>
      simp [h, TM2.step, program, TM2.stepAux, cfg, memory, comparisonTapes, base, bank, Function.update_apply] <;>
      congr 2 <;> funext k <;> cases k <;> simp [Function.update_apply, bank]
  have run := (((Run.exact h₁).trans (Run.exact h₂)).trans (Run.exact h₃)).trans h₄
  have hm := max_le ha hb
  by_cases h : a < b
  · simp only [h, ite_true] at run ⊢
    have finish := replace_run true true input saved (encodeNat a) (encodeNat b)
    exact (run.trans finish).mono (by simp [base, bank, copySrc, comparisonTapes]; omega)
  · simp only [h, ite_false] at run ⊢
    have finish := candidate_clear true true input saved (encodeNat a) (encodeNat b)
    exact (run.trans finish).mono (by simp [base, bank, copySrc, comparisonTapes]; omega)

theorem update_run (ok : Bool) (q : Option ℕ) (input saved : List Bool) (a W : ℕ)
    (ha : (encodeNat a).length ≤ W) (hq : ChosenBound q W) :
    Run (cfg .choose (memory q.isSome ok)
        (bank input saved [] (encodeNat a) (encodeNat (q.getD 0)) 0 0))
      (cfg .outer (memory (if ok then insert q a else q).isSome ok)
        (bank input saved [] [] (encodeNat ((if ok then insert q a else q).getD 0)) 0 0))
      (10 * W + 20) := by
  cases ok with
  | false =>
    have h₀ : Run (cfg .choose (memory q.isSome false)
        (bank input saved [] (encodeNat a) (encodeNat (q.getD 0)) 0 0))
      (cfg (.clear .candidate) (memory q.isSome false)
        (bank input saved [] (encodeNat a) (encodeNat (q.getD 0)) 0 0)) 1 := Run.one rfl
    have h₁ := candidate_clear q.isSome false input saved (encodeNat a) (encodeNat (q.getD 0))
    exact (h₀.trans h₁).mono (by omega)
  | true =>
    cases q with
    | none =>
      have h₀ : Run (cfg .choose (memory false true) (bank input saved [] (encodeNat a) [] 0 0))
          (cfg (.copyMove .chosen) (memory false true) (bank input saved [] (encodeNat a) [] 0 0)) 1 :=
        Run.one rfl
      exact (h₀.trans (record_run false true input saved (encodeNat a))).mono (by omega)
    | some b =>
      have h₀ : Run (cfg .choose (memory true true)
          (bank input saved [] (encodeNat a) (encodeNat b) 0 0))
          (cfg (.copyMove .minLeft) (memory true true)
            (bank input saved [] (encodeNat a) (encodeNat b) 0 0)) 1 := Run.one rfl
      have hr := h₀.trans (minimum_run input saved a b W ha (hq b rfl))
      have bounded := hr.mono (show 1 + (10 * W + 19) ≤ 10 * W + 20 by omega)
      by_cases h : a < b <;>
        simpa [insert, h] using bounded

theorem outer_nonempty (m : Memory) (t : Stack → List Bool) (h : t .input ≠ []) :
    Run (cfg .outer m t) (cfg (.scan .candidate) m t) 1 := by
  apply Run.one
  change TM2.step program _ = _
  cases hx : t .input with
  | nil => exact False.elim (h hx)
  | cons b bs => simp [TM2.step, program, TM2.stepAux, cfg, hx]

theorem finish_run (q : Option ℕ) (previous : Bool) (saved : List Bool) :
    Run (cfg .outer (memory q.isSome previous) (bank [] saved [] [] (encodeNat (q.getD 0)) 0 0))
      ⟨none, (none, memory q.isSome previous), bank [] [] [] [] (encodeNat (q.getD 0)) 0 0⟩
      (saved.length + 3) := by
  have h₀ : Run (cfg .outer (memory q.isSome previous) (bank [] saved [] [] (encodeNat (q.getD 0)) 0 0))
      (cfg (.clear .saved) (memory q.isSome previous) (bank [] saved [] [] (encodeNat (q.getD 0)) 0 0)) 1 :=
    Run.one rfl
  have h₁ := clear_run .saved (memory q.isSome previous) (bank [] saved [] [] (encodeNat (q.getD 0)) 0 0)
  have e : Function.update (bank [] saved [] [] (encodeNat (q.getD 0)) 0 0) (clearStack .saved) [] =
      bank [] [] [] [] (encodeNat (q.getD 0)) 0 0 := by funext k; cases k <;> rfl
  rw [e] at h₁
  have h₂ : Run (cfg .finish (memory q.isSome previous) (bank [] [] [] [] (encodeNat (q.getD 0)) 0 0))
      ⟨none, (none, memory q.isSome previous), bank [] [] [] [] (encodeNat (q.getD 0)) 0 0⟩ 1 := Run.one rfl
  exact (h₀.trans ((Run.exact h₁).trans h₂)).mono (by dsimp [bank, clearStack]; omega)

def iterationBound (all : List ℕ) (W : ℕ) : ℕ :=
  2 * (words all).length + all.length * (5 * W + 8) + 12 * W + 29

/-- The outer loop has an actual run for every finite ordered list, including
duplicates and zero, and a minimum retained from a previous prefix. -/
theorem select_run (all xs : List ℕ) (q : Option ℕ) (previous : Bool) (W : ℕ)
    (hall : ∀ b ∈ all, (encodeNat b).length ≤ W)
    (hxs : ∀ b ∈ xs, (encodeNat b).length ≤ W) (hq : ChosenBound q W) :
    ∃ endingFlag,
      Run (cfg .outer (memory q.isSome previous)
          (bank (words xs) (words all) [] [] (encodeNat (q.getD 0)) 0 0))
        ⟨none, (none, memory (select (eligible all) xs q).isSome endingFlag),
          bank [] [] [] [] (encodeNat ((select (eligible all) xs q).getD 0)) 0 0⟩
        (xs.length * iterationBound all W + (words all).length + 3) := by
  induction xs generalizing q previous with
  | nil => exact ⟨previous, by simpa [select] using finish_run q previous (words all)⟩
  | cons a as ih =>
    have ha := hxs a (by simp)
    let next := if eligible all a then insert q a else q
    have hn : ChosenBound next W := by
      dsimp only [next]
      split
      · exact insert_bound q a W hq ha
      · exact hq
    have h₀ := outer_nonempty (memory q.isSome previous)
      (bank (words (a :: as)) (words all) [] [] (encodeNat (q.getD 0)) 0 0) (words_cons_ne_nil a as)
    have h₁ := frame_run .candidate (memory q.isSome previous)
      (bank (words (a :: as)) (words all) [] [] (encodeNat (q.getD 0)) 0 0)
      (encodeNat a) (words as) rfl rfl rfl
    have e₁ : Function.update (Function.update
        (bank (words (a :: as)) (words all) [] [] (encodeNat (q.getD 0)) 0 0)
        (frameSrc .candidate) (words as)) (frameDst .candidate) (encodeNat a) =
        bank (words as) (words all) [] (encodeNat a) (encodeNat (q.getD 0)) 0 0 := by
      funext k; cases k <;> rfl
    rw [e₁] at h₁
    have h₂ := copy_run .inner (memory q.isSome previous)
      (bank (words as) (words all) [] (encodeNat a) (encodeNat (q.getD 0)) 0 0) rfl rfl
    have e₂ : Function.update (bank (words as) (words all) [] (encodeNat a) (encodeNat (q.getD 0)) 0 0)
        (copyDst .inner)
        ((bank (words as) (words all) [] (encodeNat a) (encodeNat (q.getD 0)) 0 0) (copySrc .inner)) =
        bank (words as) (words all) (words all) (encodeNat a) (encodeNat (q.getD 0)) 0 0 := by
      funext k; cases k <;> rfl
    rw [e₂] at h₂
    have h₃ := eligibility_run all q.isSome previous (words as) (words all) (encodeNat (q.getD 0)) a W ha hall
    have h₄ := update_run (eligible all a) q (words as) (words all) a W ha hq
    obtain ⟨lastFlag, h₅⟩ := ih next (eligible all a) (fun b hb => hxs b (by simp [hb])) hn
    refine ⟨lastFlag, ?_⟩
    have run := ((((h₀.trans (Run.exact h₁)).trans (Run.exact h₂)).trans h₃).trans h₄).trans h₅
    change Run _ _ _ at run
    exact run.mono (by dsimp [iterationBound, bank, copySrc]; nlinarith)

end Counting.Algorithm.KarpLubyRequest.Median.Program
