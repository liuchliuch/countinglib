import Counting.Algorithm.KarpLubyRequest.Iteration.Stages

/-!
# Exact repeated execution

The encoder, function and source-time map occur only in this proof contract.
The compiled program has only the original finite body and a physical counter.
In particular no iterate, parser, accumulator or evaluator is a TM2 instruction.
-/
namespace Counting.Algorithm.KarpLubyRequest.Iteration
open Turing Computability Holant.Complexity StackProtocol BinaryCompose IntegerArithmetic GraphPreprocessing

variable {α : Type}

/-- The actual transition total. The terminal zero test costs one transition;
each positive branch includes its test, complete borrow/restore, source call,
and two scans of the newly materialized output word. -/
def ticks (e : Encoding α Bool) (f : α → α) (sourceTime : α → ℕ) : ℕ → α → ℕ
  | 0, _ => 1
  | n + 1, x => ticks e f sourceTime n (f x) +
      (2 * ((e.encode (f x)).length + 1) +
        (sourceTime x + (2 * (borrowCount (encodeNat (n + 1)) + 1) + 1)))

/-- Complete repeated execution from a physical canonical counter and a
serialized state, conditional only on the displayed real body runs. -/
theorem run (body : Machine) (e : Encoding α Bool) (f : α → α) (sourceTime : α → ℕ)
    (hbody : ∀ x, SourceRun body (e.encode x) (e.encode (f x)) (sourceTime x))
    (n : ℕ) (x : α) :
    RunsExactly (computer body).step
      (cfg (own body 0) body.initial (ready body (encodeNat n) (e.encode x)))
      (finished body (e.encode (f^[n] x))) (ticks e f sourceTime n x) := by
  induction n generalizing x with
  | zero => exact runsExactly_one (check_zero body (e.encode x))
  | succ n ih =>
    have first := iteration body n (e.encode x) (e.encode (f x)) (sourceTime x) (hbody x)
    have rest := ih (f x)
    simpa only [ticks, Function.iterate_succ_apply] using first.trans rest

/-- Source executions and both physical output scans, in the actual forward
iteration order. -/
def bodyCharges (e : Encoding α Bool) (f : α → α) (sourceTime : α → ℕ) (n : ℕ) (x : α) : ℕ :=
  ∑ i ∈ Finset.range n, (sourceTime (f^[i] x) + 2 * ((e.encode (f^[i + 1] x)).length + 1))

/-- The binary countdown visits each positive value exactly once. -/
def counterCharges (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (2 * (borrowCount (encodeNat (k + 1)) + 1) + 1)

theorem bodyCharges_succ (e : Encoding α Bool) (f : α → α) (sourceTime : α → ℕ)
    (n : ℕ) (x : α) :
    bodyCharges e f sourceTime (n + 1) x = bodyCharges e f sourceTime n (f x) +
      (sourceTime x + 2 * ((e.encode (f x)).length + 1)) := by
  unfold bodyCharges
  rw [Finset.sum_range_succ']
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]

theorem counterCharges_succ (n : ℕ) :
    counterCharges (n + 1) = counterCharges n + (2 * (borrowCount (encodeNat (n + 1)) + 1) + 1) := by
  unfold counterCharges
  rw [Finset.sum_range_succ]

/-- Exact additive accounting, not merely an asymptotic estimate. -/
theorem ticks_eq_sum (e : Encoding α Bool) (f : α → α) (sourceTime : α → ℕ)
    (n : ℕ) (x : α) :
    ticks e f sourceTime n x = 1 + bodyCharges e f sourceTime n x + counterCharges n := by
  induction n generalizing x with
  | zero => simp [ticks, bodyCharges, counterCharges]
  | succ n ih =>
    rw [ticks, ih, bodyCharges_succ, counterCharges_succ]
    omega

theorem finished_input (body : Machine) (word : List Bool) :
    (finished body word).stk (bodyStack body body.input) = word :=
  wordTape_at body.input word

theorem finished_counter (body : Machine) (word : List Bool) :
    (finished body word).stk (counter body) = [] := rfl

theorem finished_borrow (body : Machine) (word : List Bool) :
    (finished body word).stk (borrow body) = [] := rfl

theorem finished_transfer (body : Machine) (word : List Bool) :
    (finished body word).stk (transfer body) = [] := rfl

theorem finished_body_other (body : Machine) (word : List Bool) (k : body.K) (hk : k ≠ body.input) :
    (finished body word).stk (bodyStack body k) = [] :=
  wordTape_other body.input k word hk

/-- Measured primitives execute the same actual caller. This is deliberately
not a polynomial-in-log(count) assertion for a numeric repetition loop. -/
theorem bit_cost (body : Machine) (e : Encoding α Bool) (f : α → α) (sourceTime : α → ℕ)
    (hbody : ∀ x, SourceRun body (e.encode x) (e.encode (f x)) (sourceTime x)) (n : ℕ) (x : α) :
    (Primitive.run (program body) (ticks e f sourceTime n x)
      (some (cfg (own body 0) body.initial (ready body (encodeNat n) (e.encode x))))).2 =
        some (finished body (e.encode (f^[n] x))) ∧
    (Primitive.run (program body) (ticks e f sourceTime n x)
      (some (cfg (own body 0) body.initial (ready body (encodeNat n) (e.encode x))))).1 ≤
        (8 + body.primitiveBudget) * (1 + bodyCharges e f sourceTime n x + counterCharges n) := by
  have h := Primitive.execution_cost (program body) (8 + body.primitiveBudget) (program_budget body)
    _ _ _ (run body e f sourceTime hbody n x)
  refine ⟨h.1, ?_⟩
  rw [← ticks_eq_sum e f sourceTime n x]
  exact h.2

/-- A caller may retain an arbitrary finite saved register and every stack
outside the embedding. Only exact code equations and full-bank endpoint
relations are required; source iteration is supplied by the theorem above. -/
theorem outer_run (body : Machine) (e : Encoding α Bool) (f : α → α) (sourceTime : α → ℕ)
    (hbody : ∀ x, SourceRun body (e.encode x) (e.encode (f x)) (sourceTime x))
    (n : ℕ) (x : α) {J R τ ρ : Type} [DecidableEq J]
    (st : Stack body ↪ J) (labels : Label body → R) (ret : R) (state : State body × τ ≃ ρ)
    (caller : R → TM2.Stmt (fun _ : J => Bool) R ρ)
    (code : ∀ l, caller (labels l) = MachineCall.block st labels ret state (program body l))
    (saved : τ) (frame : J → List Bool)
    (start finish : TM2.Cfg (fun _ : J => Bool) R ρ)
    (ha : Embedded.Rel st labels ret frame
      (StateAdapter.cfg state saved (cfg (own body 0) body.initial (ready body (encodeNat n) (e.encode x)))) start)
    (hz : Embedded.Rel st labels ret frame
      (StateAdapter.cfg state saved (finished body (e.encode (f^[n] x)))) finish) :
    (fun c => c.bind (TM2.step caller))^[ticks e f sourceTime n x] (some start) = some finish :=
  MachineCall.run st labels ret state (program body) caller code saved frame _ _ _ _ _ ha hz
    (run body e f sourceTime hbody n x)

end Counting.Algorithm.KarpLubyRequest.Iteration
