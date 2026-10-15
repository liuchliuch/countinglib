import Counting.Algorithm.KarpLubyRequest.Returning
import Counting.Algorithm.KarpLubyRequest.CountedList

/-!
# Returning parser contracts for actual finite programs

A verifier consumes its raw field, retains the physical ambient variable word,
and clears its owned workspace on success. The run field concerns the supplied
TM2 program itself, on every raw input; `accepts` is specification data and is
never evaluated by the generated program. This permits repeated sequential
calls and nested-list compilation without an unbounded semantic instruction.
-/
namespace Counting.Algorithm.KarpLubyRequest
open Turing Holant.Complexity StackProtocol

/-- The two caller inputs occupy distinct stacks; all other source workspaces
start empty. The original variable word is not reconstructed from its length. -/
def verifierTapes {K : Type} [DecidableEq K] (input ambient : K)
    (raw original : List Bool) : K → List Bool :=
  Function.update (Function.update (fun _ => []) input raw) ambient original

structure Verifier (K Λ : Type) [DecidableEq K] where
  input : K
  ambient : K
  distinct : input ≠ ambient
  main : Λ
  program : Λ → Stmt K Λ Bool
  accepts : List Bool → List Bool → Bool
  bound : ℕ → ℕ → ℕ
  monotone : ∀ {m n v w}, m ≤ n → v ≤ w → bound m v ≤ bound n w
  budget : ℕ
  statement_budget : ∀ label, TM2Cost.budget (program label) ≤ budget
  run : ∀ raw original, ∃ (ending : K → List Bool) (time : ℕ),
    time ≤ bound raw.length original.length ∧
    RunsExactly (TM2.step program)
      (cfg main false (verifierTapes input ambient raw original))
      (⟨none, (none, accepts raw original), ending⟩ : Cfg K Λ Bool) time ∧
    (accepts raw original = true → ending = verifierTapes input ambient [] original)

namespace Verifier
variable {K Λ : Type} [DecidableEq K]

abbrev computer [Fintype K] [Fintype Λ] (v : Verifier K Λ) : FinTM2 where
  K := K
  k₀ := v.input
  k₁ := v.input
  Γ _ := Bool
  Λ := Λ
  main := v.main
  σ := Option Bool × Bool
  initialState := (none, false)
  m := v.program

/-- Costs are accumulated by the canonical primitive interpreter over precisely
the execution certified by the source program's contract. -/
theorem bit_cost (v : Verifier K Λ) (raw original : List Bool) :
    ∃ ending time, time ≤ v.bound raw.length original.length ∧
      (GraphPreprocessing.Primitive.run v.program time
        (some (cfg v.main false (verifierTapes v.input v.ambient raw original)))).2 =
        some (⟨none, (none, v.accepts raw original), ending⟩ : Cfg K Λ Bool) ∧
      (GraphPreprocessing.Primitive.run v.program time
        (some (cfg v.main false (verifierTapes v.input v.ambient raw original)))).1 ≤
        v.budget * v.bound raw.length original.length := by
  obtain ⟨ending, time, ht, hr, _⟩ := v.run raw original
  have hc := GraphPreprocessing.Primitive.execution_cost v.program v.budget v.statement_budget
    time _ _ hr
  exact ⟨ending, time, ht, hc.1, hc.2.trans (Nat.mul_le_mul_left _ ht)⟩

end Verifier
end Counting.Algorithm.KarpLubyRequest
