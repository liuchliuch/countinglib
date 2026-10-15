import Counting.Algorithm.KarpLubyRequest.GroupOutput.Program

/-! Exact returning executions for append and finish, with literal codecs and
linear costs in the physically stored words. -/
namespace Counting.Algorithm.KarpLubyRequest.GroupOutput
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby

theorem append_cons (bit : Bool) (word acc count : List Bool) :
    computer.step (cfg .append () (bank (bit :: word) acc [] count)) =
      some (cfg .append () (bank word (bit :: true :: acc) [] count)) := by
  change TM2.step program _ = _
  change some (⟨some Label.append, (none, ()),
    Function.update (Function.update (Function.update (bank (bit :: word) acc [] count)
      0 word) 1 (true :: acc)) 1 (bit :: true :: acc)⟩ : computer.Cfg) = _
  congr 2
  funext k
  fin_cases k <;> rfl

theorem append_nil (acc count : List Bool) :
    computer.step (cfg .append () (bank [] acc [] count)) =
      some ⟨none, (none, ()), bank [] (false :: acc) [] count⟩ := by
  change TM2.step program _ = _
  change some (⟨none, (none, ()),
    Function.update (Function.update (bank [] acc [] count) 0 []) 1 (false :: acc)⟩ : computer.Cfg) = _
  congr 2
  funext k
  fin_cases k <;> rfl

/-- The delimiter and halt are executed in the last actual transition. Every
payload transition performs the two ordered pushes of a reversed frame. -/
theorem append_word (word acc count : List Bool) :
    RunsExactly computer.step (cfg .append () (bank word acc [] count))
      ⟨none, (none, ()), bank [] ((Encoding.frame word).reverse ++ acc) [] count⟩
      (word.length + 1) := by
  induction word generalizing acc with
  | nil => simpa only [reverse_frame_nil, List.singleton_append, List.length_nil] using
      runsExactly_one (append_nil acc count)
  | cons bit word ih =>
    have h := (runsExactly_one (append_cons bit word acc count)).trans (ih (bit :: true :: acc))
    simpa only [reverse_frame_cons, List.append_assoc, List.cons_append, List.nil_append,
      List.length_cons, Nat.add_assoc] using h

/-- A single actual group result is appended without reordering or deduplication.
The group-count word is preserved bit-for-bit. -/
theorem append_run (xs : List ℕ) (a : ℕ) (count : List Bool) :
    RunsExactly computer.step (cfg .append () (bank (encodeNat a) (reversed xs) [] count))
      ⟨none, (none, ()), bank [] (reversed (xs ++ [a])) [] count⟩
      ((encodeNat a).length + 1) := by
  rw [reversed_append]
  exact append_word (encodeNat a) (reversed xs) count

theorem reverse_run (word count : List Bool) :
    RunsExactly computer.step (cfg .reverse () (bank [] word.reverse [] count))
      (cfg .frameMove () (bank word [] [] count)) (word.length + 1) := by
  have h := copy_move_exact (1 : Stack) 3 0 (by decide) (by decide)
    computer.step .reverse .frameMove (by intro m t; rfl)
    () (fun _ => []) word.reverse count []
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h
  convert h using 1 <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

theorem header_run (word count : List Bool) :
    RunsExactly computer.step (cfg .frameMove () (bank word [] [] count))
      (cfg .done () (bank (Encoding.frame count ++ word) [] [] []))
      (2 * count.length + 3) := by
  have h := FixedFieldMachines.FrameEmit.prepend_exact (3 : Stack) 0 2
    (by decide) (by decide) (by decide) computer.step .frameMove .delimiter .emit .done
    (by intro m t; rfl) (by intro m t; rfl) (by intro m t; rfl)
    () (fun _ => []) count word
  rw [Contract.frame_eq]
  convert h using 1 <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

theorem done_run (word : List Bool) :
    RunsExactly computer.step (cfg .done () (bank word [] [] []))
      ⟨none, (none, ()), bank word [] [] []⟩ 1 := by
  apply runsExactly_one
  rfl

/-- Finishing consumes the count word, accumulator, and scratch. The one final
reversal restores the original order of every numerator occurrence. -/
theorem finish_words (words : List (List Bool)) (count : List Bool) :
    RunsExactly computer.step (cfg .reverse () (bank [] (body words).reverse [] count))
      ⟨none, (none, ()), bank (Encoding.frame count ++ body words) [] [] []⟩
      ((body words).length + 2 * count.length + 5) := by
  have h := ((reverse_run (body words) count).trans (header_run (body words) count)).trans
    (done_run (Encoding.frame count ++ body words))
  convert h using 1 <;> omega

/-- Exactly the canonical input accepted by the already proved median machine.
The count g is stored and processed on stack 3, never inside the finite control. -/
theorem finish_run (xs : List ℕ) :
    RunsExactly computer.step
      (cfg .reverse () (bank [] (reversed xs) [] (encodeNat xs.length)))
      ⟨none, (none, ()), bank (Median.input xs) [] [] []⟩
      ((body (xs.map encodeNat)).length + 2 * (encodeNat xs.length).length + 5) :=
  finish_words (xs.map encodeNat) (encodeNat xs.length)

def appendTime (xs : List ℕ) : ℕ := (xs.map fun a => (encodeNat a).length + 1).sum

theorem appendTime_le_body_length (xs : List ℕ) :
    appendTime xs ≤ (body (xs.map encodeNat)).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [appendTime, List.map_cons, List.sum_cons] at ih ⊢
    rw [body_cons, List.length_append, Encoding.frame_length]
    omega

theorem appended_length (xs : List ℕ) (a : ℕ) :
    (reversed (xs ++ [a])).length = (reversed xs).length + 2 * (encodeNat a).length + 1 := by
  rw [reversed_append, List.length_append, List.length_reverse, Encoding.frame_length]
  omega

theorem finish_cost (xs : List ℕ) :
    (body (xs.map encodeNat)).length + 2 * (encodeNat xs.length).length + 5 =
      (Median.input xs).length + 4 := by
  rw [Median.input_length]
  change (body (xs.map encodeNat)).length + 2 * (encodeNat xs.length).length + 5 =
    2 * (encodeNat xs.length).length + (body (xs.map encodeNat)).length + 1 + 4
  omega

/-- Primitive costs are measured on exactly the append run above. -/
theorem append_primitive_cost (xs : List ℕ) (a : ℕ) (count : List Bool) :
    (Primitive.run program ((encodeNat a).length + 1)
      (some (cfg .append () (bank (encodeNat a) (reversed xs) [] count)))).2 =
      some (⟨none, (none, ()), bank [] (reversed (xs ++ [a])) [] count⟩ : computer.Cfg) ∧
    (Primitive.run program ((encodeNat a).length + 1)
      (some (cfg .append () (bank (encodeNat a) (reversed xs) [] count)))).1 ≤
      6 * ((encodeNat a).length + 1) :=
  Primitive.execution_cost program 6 statement_budget _ _ _ (append_run xs a count)

theorem finish_primitive_cost (xs : List ℕ) :
    (Primitive.run program ((Median.input xs).length + 4)
      (some (cfg .reverse () (bank [] (reversed xs) [] (encodeNat xs.length))))).2 =
      some (⟨none, (none, ()), bank (Median.input xs) [] [] []⟩ : computer.Cfg) ∧
    (Primitive.run program ((Median.input xs).length + 4)
      (some (cfg .reverse () (bank [] (reversed xs) [] (encodeNat xs.length))))).1 ≤
      6 * ((Median.input xs).length + 4) := by
  have h := finish_run xs
  rw [finish_cost] at h
  exact Primitive.execution_cost program 6 statement_budget _ _ _ h

/-- Returning append call: exactly the four installed source stacks are touched. -/
theorem caller_append {J R : Type} [DecidableEq J] (e : Stack ↪ J)
    (labels : Label → R) (ret : R)
    (caller : R → TM2.Stmt (fun _ : J => Bool) R State)
    (code : ∀ l, caller (labels l) = Embedded.block e labels ret (program l))
    (xs : List ℕ) (a : ℕ) (count : List Bool)
    (start : TM2.Cfg (fun _ : J => Bool) R State) (frame : J → List Bool)
    (hstart : Embedded.Rel e labels ret frame
      (cfg .append () (bank (encodeNat a) (reversed xs) [] count)) start) :
    ∃ ending, (fun p => p.bind (TM2.step caller))^[(encodeNat a).length + 1] (some start) = some ending ∧
      ending.l = some ret ∧ ending.stk (e 0) = [] ∧
      ending.stk (e 1) = reversed (xs ++ [a]) ∧ ending.stk (e 2) = [] ∧
      ending.stk (e 3) = count ∧
      (∀ j, (∀ k, j ≠ e k) → ending.stk j = frame j) := by
  obtain ⟨ending, run, rel⟩ := Embedded.run e labels ret program caller code _ _ start frame _ hstart
    (append_run xs a count)
  exact ⟨ending, run, rel.1, rel.2.2.1 0, rel.2.2.1 1, rel.2.2.1 2, rel.2.2.1 3, rel.2.2.2⟩

/-- Returning finish call delivers the original Median input and clears every
selected work stack. Unselected caller stacks retain their original frame. -/
theorem caller_finish {J R : Type} [DecidableEq J] (e : Stack ↪ J)
    (labels : Label → R) (ret : R)
    (caller : R → TM2.Stmt (fun _ : J => Bool) R State)
    (code : ∀ l, caller (labels l) = Embedded.block e labels ret (program l))
    (xs : List ℕ) (start : TM2.Cfg (fun _ : J => Bool) R State) (frame : J → List Bool)
    (hstart : Embedded.Rel e labels ret frame
      (cfg .reverse () (bank [] (reversed xs) [] (encodeNat xs.length))) start) :
    ∃ ending, (fun p => p.bind (TM2.step caller))^[(Median.input xs).length + 4]
        (some start) = some ending ∧
      ending.l = some ret ∧ ending.stk (e 0) = Median.input xs ∧
      (∀ k, k ≠ (0 : Stack) → ending.stk (e k) = []) ∧
      (∀ j, (∀ k, j ≠ e k) → ending.stk j = frame j) := by
  have h := finish_run xs
  rw [finish_cost] at h
  obtain ⟨ending, run, rel⟩ := Embedded.run e labels ret program caller code _ _ start frame _ hstart h
  refine ⟨ending, run, rel.1, rel.2.2.1 0, ?_, rel.2.2.2⟩
  intro k hk
  have he := rel.2.2.1 k
  fin_cases k <;> first | exact False.elim (hk rfl) | exact he

end Counting.Algorithm.KarpLubyRequest.GroupOutput
