import Counting.Algorithm.KarpLubyRequest.LiteralVerifier
import Counting.Algorithm.KarpLubyRequest.ListVerifier
import Counting.Algorithm.KarpLubyRequest.NestedSemantics

/-!
# Both DNF list levels in one finite Boolean-stack program

Two applications of the verified compiler inline the actual literal parser into
the clause loop and that complete clause program into the formula loop. Arbitrary
raw encodings, malformed fields, contradictory clauses and repeated occurrences
are treated exactly as the original formula decoder treats them. Logical clause
normalization is a later execution stage.
-/
namespace Counting.Algorithm.KarpLubyRequest.DNFVerifier
open Turing Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby

abbrev ClauseStack := ListVerifier.Stack LiteralVerifier.Stack
abbrev ClauseLabel := ListVerifier.Label LiteralVerifier.Label
abbrev Stack := ListVerifier.Stack ClauseStack
abbrev Label := ListVerifier.Label ClauseLabel

def clause : Verifier ClauseStack ClauseLabel := ListVerifier.compile LiteralVerifier.verifier
def formula : Verifier Stack Label := ListVerifier.compile clause

abbrev computer : FinTM2 := formula.computer

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) :=
  inferInstanceAs (Fintype Bool)

theorem clause_accepts (raw original : List Bool) :
    clause.accepts raw original = NestedSemantics.clauseAccepts original.length raw := rfl

theorem formula_accepts (raw original : List Bool) :
    formula.accepts raw original = ((Encoding.formula original.length).decode raw).isSome := by
  exact NestedSemantics.formula_isSome_eq original.length raw

/-- Concrete polynomial after both compiler substitutions, in physical formula
bits and the retained explicit-variable header length. -/
def timeBound (m n : ℕ) : ℕ :=
  2 * m ^ 3 * n + 10 * m ^ 3 + 8 * m ^ 2 * n + 39 * m ^ 2 + 37 * m + 19

theorem bound_eq (m n : ℕ) : formula.bound m n = timeBound m n := by
  unfold formula clause ListVerifier.compile ListVerifier.bound LiteralVerifier.verifier
    LiteralVerifier.bound LiteralFields.timeBound CountedList.Full.timeBound timeBound
  dsimp
  ring

theorem statement_budget (label : Label) : TM2Cost.budget (computer.m label) ≤ 10 :=
  formula.statement_budget label

/-- Every raw formula halts with exactly the original decoder's success bit.
The input variable word is a real second stack, not an uncharged natural oracle. -/
theorem run (raw original : List Bool) :
    ∃ ending time, time ≤ timeBound raw.length original.length ∧
      RunsExactly computer.step
        (cfg computer.main false (verifierTapes formula.input formula.ambient raw original))
        (⟨none, (none, ((Encoding.formula original.length).decode raw).isSome), ending⟩ : computer.Cfg) time ∧
      (((Encoding.formula original.length).decode raw).isSome = true →
        ending = verifierTapes formula.input formula.ambient [] original) := by
  simpa only [FinTM2.step, computer, Verifier.computer, bound_eq, formula_accepts] using formula.run raw original

/-- Actual primitive bit instructions accumulated along the same complete run. -/
theorem bit_cost (raw original : List Bool) :
    ∃ ending time, time ≤ timeBound raw.length original.length ∧
      (GraphPreprocessing.Primitive.run computer.m time
        (some (cfg computer.main false (verifierTapes formula.input formula.ambient raw original)))).2 =
        some (⟨none, (none, ((Encoding.formula original.length).decode raw).isSome), ending⟩ : computer.Cfg) ∧
      (GraphPreprocessing.Primitive.run computer.m time
        (some (cfg computer.main false (verifierTapes formula.input formula.ambient raw original)))).1 ≤
        10 * timeBound raw.length original.length := by
  have hb : formula.budget = 10 := rfl
  simpa only [computer, Verifier.computer, hb, bound_eq, formula_accepts] using formula.bit_cost raw original

/-- The two-parameter polynomial is bounded by a degree-four polynomial in the
complete encoded request whenever its two physical fields fit that request. -/
theorem encoded_bound (raw original : List Bool) (N : ℕ)
    (hm : raw.length ≤ N) (hn : original.length ≤ N) :
    timeBound raw.length original.length ≤ 2 * N ^ 4 + 18 * N ^ 3 + 39 * N ^ 2 + 37 * N + 19 := by
  have h := formula.monotone hm hn
  rw [bound_eq, bound_eq] at h
  convert h using 1 <;> unfold timeBound <;> ring

end Counting.Algorithm.KarpLubyRequest.DNFVerifier
