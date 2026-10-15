import Counting.Algorithm.KarpLubyRequest.Iteration.Program

/-! # Exact source calls, binary countdown, and ordered word transfer -/
namespace Counting.Algorithm.KarpLubyRequest.Iteration
open Turing Computability Holant.Complexity StackProtocol BinaryCompose IntegerArithmetic

/-- A real clean source execution, with its supplied finite machine unchanged. -/
def SourceRun (body : Machine) (input output : List Bool) (time : ℕ) : Prop :=
  (fun c => c.bind body.computer.step)^[time]
    (some (initList body.computer input)) = some (haltList body.computer output)

theorem check_zero (body : Machine) (word : List Bool) :
    (computer body).step (cfg (own body 0) body.initial (ready body [] word)) =
      some (finished body word) := by
  change some (TM2.stepAux (check body) (none, body.initial) (ready body [] word)) = _
  simp [check, TM2.stepAux, ready, tapes, counter, finished]

theorem check_positive (body : Machine) (word count : List Bool) (hc : count ≠ []) :
    (computer body).step (cfg (own body 0) body.initial (ready body count word)) =
      some (cfg (own body 1) body.initial (ready body count word)) := by
  cases count with
  | nil => contradiction
  | cons bit rest =>
    change some (TM2.stepAux (check body) (none, body.initial) (ready body (bit :: rest) word)) = _
    simp [check, TM2.stepAux, ready, tapes, counter, cfg]

private theorem as_counter (body : Machine) (count word : List Bool) :
    tapes3 (ready body [] word) (counter body) (transfer body) (borrow body) count [] [] =
      ready body count word := by
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => rfl

set_option backward.isDefEq.respectTransparency false in
/-- Borrow and restore are the frozen real countdown instructions; the state
word and all source-machine stacks are untouched by these loops. -/
theorem decrement (body : Machine) (count word : List Bool) :
    RunsExactly (computer body).step (cfg (own body 1) body.initial (ready body count word))
      (cfg (bodyLabel body body.main) body.initial (ready body (IntegerArithmetic.decrement count) word))
      (2 * (borrowCount count + 1)) := by
  have hb : ExecutesAt (computer body).step (own body 1)
      (CountedList.Counter.decrementStmt (counter body) (borrow body) (own body 1) (own body 2)) := by
    intro state stack; rfl
  have hr : ExecutesAt (computer body).step (own body 2)
      (copyMoveStmt (borrow body) (counter body) (own body 2) (bodyLabel body body.main)) := by
    intro state stack; rfl
  have run := CountedList.Counter.decrement_exact (counter body) (transfer body) (borrow body)
    (fun h => (show (0 : Fin 3) ≠ 2 by decide) (Sum.inl.inj h))
    (fun h => (show (0 : Fin 3) ≠ 1 by decide) (Sum.inl.inj h))
    (fun h => (show (2 : Fin 3) ≠ 1 by decide) (Sum.inl.inj h))
    (computer body).step (own body 1) (own body 2)
    (bodyLabel body body.main) hb body.initial (ready body [] word) hr count []
  rw [as_counter body count word,
    as_counter body (IntegerArithmetic.decrement count) word] at run
  exact run

theorem decrement_succ (body : Machine) (n : ℕ) (word : List Bool) :
    RunsExactly (computer body).step (cfg (own body 1) body.initial (ready body (encodeNat (n + 1)) word))
      (cfg (bodyLabel body body.main) body.initial (ready body (encodeNat n) word))
      (2 * (borrowCount (encodeNat (n + 1)) + 1)) := by
  simpa only [decrement_encodeNat, Nat.add_sub_cancel] using decrement body (encodeNat (n + 1)) word

/-- Execute the complete supplied source, preserving the physical countdown
and both caller work stacks. A clean source endpoint restores its initial state. -/
theorem call (body : Machine) (count input output : List Bool) (time : ℕ)
    (hr : SourceRun body input output time) :
    RunsExactly (computer body).step
      (cfg (bodyLabel body body.main) body.initial (ready body count input))
      (cfg (own body 3) body.initial (returned body count output)) time := by
  have ha : Embedded.Rel (bodyStack body) (bodyLabel body) (own body 3) (ready body count [])
      (StateAdapter.cfg (bodyState body) none (initList body.computer input))
      (cfg (bodyLabel body body.main) body.initial (ready body count input)) := by
    rw [Machine.init_eq]
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro k hk
      cases k with
      | inl k => rfl
      | inr k => exact False.elim (hk k rfl)
  have hz : Embedded.Rel (bodyStack body) (bodyLabel body) (own body 3) (ready body count [])
      (StateAdapter.cfg (bodyState body) none (haltList body.computer output))
      (cfg (own body 3) body.initial (returned body count output)) := by
    rw [Machine.halt_eq]
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro k hk
      cases k with
      | inl k => rfl
      | inr k => exact False.elim (hk k rfl)
  exact MachineCall.run (bodyStack body) (bodyLabel body) (own body 3) (bodyState body)
    body.program (program body) (body_code body) none (ready body count []) _ _ _ _ time ha hz hr

private theorem bodyStack_apply (body : Machine) (k : body.K) :
    bodyStack body k = Sum.inr k := rfl

private theorem as_returned (body : Machine) (count word : List Bool) :
    tapes3 (fun _ => []) (bodyStack body body.output) (counter body) (transfer body) word count [] =
      returned body count word := by
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k =>
    by_cases hk : k = body.output <;>
      simp [tapes3, returned, tapes, bodyStack_apply, counter, transfer, wordTape, Function.update_apply, hk]

private theorem as_moving_output (body : Machine) (count word : List Bool) :
    tapes3 (fun _ => []) (bodyStack body body.output) (counter body) (transfer body) [] count word =
      moving body count word := by
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k =>
    by_cases hk : k = body.output <;>
      simp [tapes3, moving, tapes, bodyStack_apply, counter, transfer, Function.update_apply, hk]

private theorem as_moving_input (body : Machine) (count word : List Bool) :
    tapes3 (fun _ => []) (transfer body) (counter body) (bodyStack body body.input) word count [] =
      moving body count word := by
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k =>
    by_cases hk : k = body.input <;>
      simp [tapes3, moving, tapes, bodyStack_apply, counter, transfer, Function.update_apply, hk]

private theorem as_ready (body : Machine) (count word : List Bool) :
    tapes3 (fun _ => []) (transfer body) (counter body) (bodyStack body body.input) [] count word =
      ready body count word := by
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k =>
    by_cases hk : k = body.input <;>
      simp [tapes3, ready, tapes, bodyStack_apply, counter, transfer, wordTape, Function.update_apply, hk]

set_option backward.isDefEq.respectTransparency false in
/-- Transfer is two complete physical passes even when input and output are
the same stack. After the first pass every body stack is empty. -/
theorem transfer_exact (body : Machine) (count word : List Bool) :
    RunsExactly (computer body).step (cfg (own body 3) body.initial (returned body count word))
      (cfg (own body 0) body.initial (ready body count word)) (2 * (word.length + 1)) := by
  have hm : ExecutesAt (computer body).step (own body 3)
      (copyMoveStmt (bodyStack body body.output) (transfer body) (own body 3) (own body 4)) := by
    intro state stack; rfl
  have hr : ExecutesAt (computer body).step (own body 4)
      (copyMoveStmt (transfer body) (bodyStack body body.input) (own body 4) (own body 0)) := by
    intro state stack; rfl
  have first : RunsExactly (computer body).step
      (cfg (own body 3) body.initial (returned body count word))
      (cfg (own body 4) body.initial (moving body count word.reverse)) (word.length + 1) := by
    have h := copy_move_exact (bodyStack body body.output) (counter body) (transfer body)
        (by intro h; cases h) (by intro h; cases h) (computer body).step (own body 3) (own body 4)
        hm body.initial (fun _ => []) word count []
    simp only [List.append_nil] at h
    rw [as_returned body count word, as_moving_output body count word.reverse] at h
    exact h
  have last : RunsExactly (computer body).step
      (cfg (own body 4) body.initial (moving body count word.reverse))
      (cfg (own body 0) body.initial (ready body count word)) (word.length + 1) := by
    have h := copy_move_exact (transfer body) (counter body) (bodyStack body body.input)
        (fun h => (show (2 : Fin 3) ≠ 0 by decide) (Sum.inl.inj h))
        (by intro h; cases h) (computer body).step (own body 4) (own body 0)
        hr body.initial (fun _ => []) word.reverse count []
    simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h
    rw [as_moving_input body count word.reverse, as_ready body count word] at h
    exact h
  convert first.trans last using 1 <;> omega

theorem counter_nonempty (n : ℕ) : encodeNat (n + 1) ≠ [] := by
  intro h
  have h' := congrArg decodeNat h
  rw [decode_encodeNat] at h'
  change n + 1 = 0 at h'
  omega

/-- One complete positive iteration, with every caller operation charged. -/
theorem iteration (body : Machine) (n : ℕ) (input output : List Bool) (time : ℕ)
    (hr : SourceRun body input output time) :
    RunsExactly (computer body).step
      (cfg (own body 0) body.initial (ready body (encodeNat (n + 1)) input))
      (cfg (own body 0) body.initial (ready body (encodeNat n) output))
      (2 * (output.length + 1) + (time + (2 * (borrowCount (encodeNat (n + 1)) + 1) + 1))) := by
  have first := runsExactly_one (check_positive body input (encodeNat (n + 1)) (counter_nonempty n))
  exact ((first.trans (decrement_succ body n input)).trans
    (call body (encodeNat n) input output time hr)).trans (transfer_exact body (encodeNat n) output)

end Counting.Algorithm.KarpLubyRequest.Iteration
