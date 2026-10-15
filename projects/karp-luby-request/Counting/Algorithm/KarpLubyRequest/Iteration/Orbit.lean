import Counting.Algorithm.KarpLubyRequest.Iteration.Cost

/-!
# Repetition with operational certificates on the visited states

A sample body needs enough physical random bits for its next trial. It need not
claim successful trial semantics on arbitrary short words. This theorem asks
for actual source runs only at the states visited by the requested repetition.
A typed tape/budget invariant can establish these premises without changing
the compiler or padding any unavailable random bit.
-/
namespace Counting.Algorithm.KarpLubyRequest.Iteration
open Turing Computability Holant.Complexity StackProtocol BinaryCompose GraphPreprocessing
variable {α : Type}

/-- Every assumed execution is a concrete clean run of the supplied finite
body. No source execution is required beyond the visited orbit prefix. -/
theorem run_on (body : Machine) (e : Encoding α Bool) (f : α → α) (sourceTime : α → ℕ)
    (n : ℕ) (x : α)
    (hbody : ∀ i < n, SourceRun body (e.encode (f^[i] x))
      (e.encode (f (f^[i] x))) (sourceTime (f^[i] x))) :
    RunsExactly (computer body).step
      (cfg (own body 0) body.initial (ready body (encodeNat n) (e.encode x)))
      (finished body (e.encode (f^[n] x))) (ticks e f sourceTime n x) := by
  induction n generalizing x with
  | zero => exact runsExactly_one (check_zero body (e.encode x))
  | succ n ih =>
    have first : SourceRun body (e.encode x) (e.encode (f x)) (sourceTime x) := hbody 0 (by omega)
    have more : ∀ i < n, SourceRun body (e.encode (f^[i] (f x)))
        (e.encode (f (f^[i] (f x)))) (sourceTime (f^[i] (f x))) := by
      intro i hi
      simpa only [Function.iterate_succ_apply] using hbody (i + 1) (by omega)
    have head := iteration body n (e.encode x) (e.encode (f x)) (sourceTime x) first
    have tail := ih (f x) more
    simpa only [ticks, Function.iterate_succ_apply] using head.trans tail

theorem bit_cost_on (body : Machine) (e : Encoding α Bool) (f : α → α) (sourceTime : α → ℕ)
    (n : ℕ) (x : α)
    (hbody : ∀ i < n, SourceRun body (e.encode (f^[i] x))
      (e.encode (f (f^[i] x))) (sourceTime (f^[i] x))) :
    (Primitive.run (program body) (ticks e f sourceTime n x)
      (some (cfg (own body 0) body.initial (ready body (encodeNat n) (e.encode x))))).2 =
        some (finished body (e.encode (f^[n] x))) ∧
    (Primitive.run (program body) (ticks e f sourceTime n x)
      (some (cfg (own body 0) body.initial (ready body (encodeNat n) (e.encode x))))).1 ≤
        (8 + body.primitiveBudget) * ticks e f sourceTime n x :=
  Primitive.execution_cost (program body) (8 + body.primitiveBudget) (program_budget body)
    _ _ _ (run_on body e f sourceTime n x hbody)

theorem bounded_bit_cost_on (body : Machine) (e : Encoding α Bool) (f : α → α) (sourceTime : α → ℕ)
    (n : ℕ) (x : α)
    (hbody : ∀ i < n, SourceRun body (e.encode (f^[i] x))
      (e.encode (f (f^[i] x))) (sourceTime (f^[i] x)))
    (bodyBound wordBound : ℕ)
    (ht : ∀ i < n, sourceTime (f^[i] x) ≤ bodyBound)
    (hw : ∀ i < n, (e.encode (f^[i + 1] x)).length ≤ wordBound) :
    (Primitive.run (program body) (ticks e f sourceTime n x)
      (some (cfg (own body 0) body.initial (ready body (encodeNat n) (e.encode x))))).1 ≤
        (8 + body.primitiveBudget) *
          (1 + n * (bodyBound + 2 * (wordBound + 1) + 2 * (encodeNat n).length + 3)) :=
  (bit_cost_on body e f sourceTime n x hbody).2.trans
    (Nat.mul_le_mul_left _ (ticks_le e f sourceTime n x bodyBound wordBound ht hw))

/-- Actual embedding of orbit-local repetition, retaining every caller stack
outside `st` and the arbitrary saved register throughout the complete run. -/
theorem outer_run_on (body : Machine) (e : Encoding α Bool) (f : α → α) (sourceTime : α → ℕ)
    (n : ℕ) (x : α)
    (hbody : ∀ i < n, SourceRun body (e.encode (f^[i] x))
      (e.encode (f (f^[i] x))) (sourceTime (f^[i] x)))
    {J R τ ρ : Type} [DecidableEq J]
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
    (run_on body e f sourceTime n x hbody)

end Counting.Algorithm.KarpLubyRequest.Iteration
