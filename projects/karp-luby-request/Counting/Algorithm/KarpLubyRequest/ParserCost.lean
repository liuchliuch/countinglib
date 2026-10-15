import Counting.Algorithm.KarpLubyRequest.ProblemHeader
import Counting.Algorithm.KarpLubyRequest.CountedList

/-!
# Actual primitive instruction costs of connected parser executions

These statements instrument the very same finite programs proved to run in the
parser modules. H1's primitive interpreter charges each push, pop, peek, load,
branch, goto, and halt, and refines actual `TM2.step`. All control types in the
programs here are finite; arithmetic on unbounded natural numbers is not a
transition callback. No parser prefix is called the whole-request FPRAS.
-/
namespace Counting.Algorithm.KarpLubyRequest.ParserCost

open Turing
open Holant.Complexity GraphPreprocessing

/-- Includes every successful or failed outer-frame scan and final halt. -/
theorem outer (raw : List Bool) :
    ∃ (saved : OuterDecoder.Stack → List Bool) (time : ℕ), time ≤ raw.length + 4 ∧
      (Primitive.run OuterDecoder.program time (some (initList OuterDecoder.computer raw))).2 =
        some (⟨none, (none, ()), saved⟩ : OuterDecoder.Config) ∧
      (Primitive.run OuterDecoder.program time (some (initList OuterDecoder.computer raw))).1 ≤
        8 * (raw.length + 4) := by
  obtain ⟨saved, time, ht, hr⟩ := OuterDecoder.terminates raw
  have hc := Primitive.execution_cost OuterDecoder.program 8 OuterDecoder.statement_budget
    time (initList OuterDecoder.computer raw) (⟨none, (none, ()), saved⟩ : OuterDecoder.Config) hr
  exact ⟨saved, time, ht, hc.1, hc.2.trans (Nat.mul_le_mul_left 8 ht)⟩

/-- Includes outer framing, both rational structure checks, and status-bearing
halt on one finite program. Original raw natural-word semantics are preserved. -/
theorem preamble (raw : List Bool) :
    ∃ (saved : Preamble.Stack → List Bool) (time : ℕ), time ≤ 2 * raw.length + 20 ∧
      (Primitive.run Preamble.program time (some (initList Preamble.computer raw))).2 =
        some (⟨none, (none, (Preamble.separate raw).isSome), saved⟩ : Preamble.Config) ∧
      (Primitive.run Preamble.program time (some (initList Preamble.computer raw))).1 ≤
        10 * (2 * raw.length + 20) := by
  obtain ⟨saved, time, ht, hr⟩ := Preamble.terminates raw
  have hc := Primitive.execution_cost Preamble.program 10 Preamble.statement_budget
    time (initList Preamble.computer raw)
    (⟨none, (none, (Preamble.separate raw).isSome), saved⟩ : Preamble.Config) hr
  exact ⟨saved, time, ht, hc.1, hc.2.trans (Nat.mul_le_mul_left 10 ht)⟩

/-- Includes the compiled preamble, real success/failure dispatch, variable
header scan, and final halt; mixed unary bit patterns and unused variables remain. -/
theorem problemHeader (raw : List Bool) :
    ∃ (saved : ProblemHeader.Stack → List Bool) (time : ℕ), time ≤ 3 * raw.length + 24 ∧
      (Primitive.run ProblemHeader.computer.m time (some (initList ProblemHeader.computer raw))).2 =
        some (⟨none, (none, (ProblemHeader.separate raw).isSome), saved⟩ : ProblemHeader.Config) ∧
      (Primitive.run ProblemHeader.computer.m time (some (initList ProblemHeader.computer raw))).1 ≤
        10 * (3 * raw.length + 24) := by
  obtain ⟨saved, time, ht, hr⟩ := ProblemHeader.terminates raw
  have hc := Primitive.execution_cost ProblemHeader.computer.m 10 ProblemHeader.statement_budget
    time (initList ProblemHeader.computer raw)
    (⟨none, (none, (ProblemHeader.separate raw).isSome), saved⟩ : ProblemHeader.Config) hr
  exact ⟨saved, time, ht, hc.1, hc.2.trans (Nat.mul_le_mul_left 10 ht)⟩

end Counting.Algorithm.KarpLubyRequest.ParserCost
