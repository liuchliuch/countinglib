import Counting.Algorithm.KarpLubyRequest.ParameterProgram

/-!
# Execution interfaces for the connected parameter parser

The complete raw request is executed in the parameter machine itself, retaining
its source bank and finite comparison register. The following arithmetic stages
therefore consume fields produced by that same run.
-/
namespace Counting.Algorithm.KarpLubyRequest.ParameterParser
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby
open ParameterProgram

def bank (source : RequestParser.Stack → List Bool) (work : Fin 10 → List Bool) : Stack → List Bool :=
  Sum.elim source work

private theorem initial_rel (raw : List Bool) :
    Embedded.Rel parserMap parserLabel (control 0) (fun _ => [])
      (StateAdapter.cfg parserState BinaryArithmetic.Comparison.initial
        (initList RequestParser.computer raw)) (initList computer raw) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro k
    change (if parserMap k = parserMap RequestParser.computer.k₀ then raw else []) =
      (if k = RequestParser.computer.k₀ then raw else [])
    simp only [parserMap.injective.eq_iff]
  · intro j hj
    cases j with
    | inl k => exact False.elim (hj k rfl)
    | inr k => rfl

/-- The complete source parser actually runs inside the parameter program,
with exactly its original transition count. The added arithmetic bank is empty
and the comparison register is reset when the dispatch label is reached. -/
theorem parser_run (raw : List Bool) :
    ∃ ending time, time ≤ RequestParser.timeBound raw.length ∧
      RunsExactly computer.step (initList computer raw)
        (cfg (control 0) ((ProgramEncoding.request.decode raw).isSome,
          BinaryArithmetic.Comparison.initial) (bank ending (fun _ => []))) time ∧
      (∀ f, ProblemHeader.separate raw = some f →
        ∀ k, ending (RequestParser.headerMap k) = RequestParser.outputTapes f k) := by
  obtain ⟨ending, time, ht, hr, keep⟩ := RequestParser.terminates raw
  have hs := StateAdapter.run parserState RequestParser.computer.m
    BinaryArithmetic.Comparison.initial _ _ time hr
  have code : ∀ l, program (parserLabel l) = Embedded.block parserMap parserLabel (control 0)
      ((StateAdapter.program parserState RequestParser.computer.m) l) := by intro l; rfl
  obtain ⟨last, hl, hrel⟩ := Embedded.run parserMap parserLabel (control 0)
    (StateAdapter.program parserState RequestParser.computer.m) program code _ _
    (initList computer raw) (fun _ => []) time (initial_rel raw) hs
  have htape : last.stk = bank ending (fun _ => []) := by
    funext k
    cases k with
    | inl k => exact hrel.2.2.1 k
    | inr k => exact hrel.2.2.2 (.inr k) (fun j => by simp only [parserMap_apply, ne_eq, reduceCtorEq, not_false_eq_true])
  have he : last = cfg (control 0) ((ProgramEncoding.request.decode raw).isSome,
      BinaryArithmetic.Comparison.initial) (bank ending (fun _ => [])) := by
    rcases last with ⟨label, state, tape⟩
    have hlab := hrel.1
    have hstate := hrel.2.1
    change label = some (control 0) at hlab
    change state = (none, (ProgramEncoding.request.decode raw).isSome,
      BinaryArithmetic.Comparison.initial) at hstate
    change tape = bank ending (fun _ => []) at htape
    subst label state tape
    rfl
  refine ⟨ending, time, ht, ?_, keep⟩
  change RunsExactly computer.step _ _ time at hl
  exact he ▸ hl

/-- Prepared operand stacks of the canonical comparator, in the caller bank. -/
def comparisonTapes (frame : Stack → List Bool) (left right answer : List Bool) : Stack → List Bool :=
  Function.update (Function.update (Function.update (Function.update frame (extra 5) left)
    (extra 6) right) (extra 9) []) (extra 7) answer

/-- Each unsigned comparison is the actual H1 source program inlined into the
same parameter machine. Both operand words are consumed, one answer bit is
written, and every other caller stack and the saved parser flag is preserved. -/
theorem comparison_run (strict flag : Bool) (frame : Stack → List Bool) (a b : ℕ) :
    RunsExactly computer.step
      (cfg (compareLabel strict ()) (flag, BinaryArithmetic.Comparison.initial)
        (comparisonTapes frame (encodeNat a) (encodeNat b) []))
      (cfg (returnCompare strict) (flag, BinaryArithmetic.Comparison.initial)
        (comparisonTapes frame [] [] [decide (a < b)]))
      (max (encodeNat a).length (encodeNat b).length + 1) := by
  let first := BinaryArithmetic.Comparison.cfg (some ()) false (encodeNat a) (encodeNat b) []
  let lastSource := BinaryArithmetic.Comparison.cfg none false [] [] [decide (a < b)]
  have sourceRun := BinaryArithmetic.Comparison.compute_encodeNat_exact a b
  have adapted := StateAdapter.run comparisonState BinaryArithmetic.Comparison.computer.m
    (none, flag) first lastSource _ sourceRun
  have code : ∀ l, program (compareLabel strict l) =
      Embedded.block comparisonMap (compareLabel strict) (returnCompare strict)
        ((StateAdapter.program comparisonState BinaryArithmetic.Comparison.computer.m) l) := by
    intro l; cases l; rfl
  have hi : Embedded.Rel comparisonMap (compareLabel strict) (returnCompare strict) frame
      (StateAdapter.cfg comparisonState (none, flag) first)
      (cfg (compareLabel strict ()) (flag, BinaryArithmetic.Comparison.initial)
        (comparisonTapes frame (encodeNat a) (encodeNat b) [])) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; cases k <;> simp [cfg, comparisonTapes, comparisonMap, extra, first,
        StateAdapter.cfg, BinaryArithmetic.Comparison.cfg, BinaryArithmetic.Addition.tapes]
    · intro j hj
      have h5 := hj BinaryArithmetic.Addition.Stack.left
      have h6 := hj BinaryArithmetic.Addition.Stack.right
      have h9 := hj BinaryArithmetic.Addition.Stack.work
      have h7 := hj BinaryArithmetic.Addition.Stack.out
      change j ≠ extra 5 at h5
      change j ≠ extra 6 at h6
      change j ≠ extra 9 at h9
      change j ≠ extra 7 at h7
      simp only [cfg, comparisonTapes, Function.update_apply, h5, h6, h9, h7, ite_false]
  obtain ⟨last, run, hrel⟩ := Embedded.run comparisonMap (compareLabel strict) (returnCompare strict)
    (StateAdapter.program comparisonState BinaryArithmetic.Comparison.computer.m) program code
    _ _ _ frame _ hi adapted
  have htape : last.stk = comparisonTapes frame [] [] [decide (a < b)] := by
    funext k
    by_cases h5 : k = extra 5
    · subst k; exact hrel.2.2.1 BinaryArithmetic.Addition.Stack.left
    by_cases h6 : k = extra 6
    · subst k; exact hrel.2.2.1 BinaryArithmetic.Addition.Stack.right
    by_cases h9 : k = extra 9
    · subst k; exact hrel.2.2.1 BinaryArithmetic.Addition.Stack.work
    by_cases h7 : k = extra 7
    · subst k; exact hrel.2.2.1 BinaryArithmetic.Addition.Stack.out
    have hn := hrel.2.2.2 k (by intro j; cases j <;> assumption)
    simpa only [comparisonTapes, Function.update_apply, h5, h6, h9, h7, ite_false] using hn
  have he : last = cfg (returnCompare strict) (flag, BinaryArithmetic.Comparison.initial)
      (comparisonTapes frame [] [] [decide (a < b)]) := by
    rcases last with ⟨label, state, tape⟩
    have hlab := hrel.1
    have hstate := hrel.2.1
    change label = some (returnCompare strict) at hlab
    change state = (none, flag, BinaryArithmetic.Comparison.initial) at hstate
    change tape = comparisonTapes frame [] [] [decide (a < b)] at htape
    subst label state tape
    rfl
  change RunsExactly computer.step _ _ _ at run
  exact he ▸ run

end Counting.Algorithm.KarpLubyRequest.ParameterParser
