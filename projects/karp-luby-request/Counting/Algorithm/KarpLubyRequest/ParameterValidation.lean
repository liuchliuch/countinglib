import Counting.Algorithm.KarpLubyRequest.ParameterParser

/-!
# Complete executions of the existing binary parameter validator

This file supplies calling-context execution proofs for the already connected
`ParameterProgram.computer`. It does not define a second parameter machine.
-/
namespace Counting.Algorithm.KarpLubyRequest.ParameterValidation
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby
open ParameterProgram ParameterParser

/-- A field's literal retained raw word, indexed in the original parser bank. -/
def rawField (source : RequestParser.Stack → List Bool) (i : Fin 4) : List Bool :=
  source (RequestParser.headerMap (.inl (![5, 2, 7, 3] i)))

/-- The four canonical results are installed in order; all other work stacks
remain physically empty. The original parser bank is retained without changes. -/
def prepared (source : RequestParser.Stack → List Bool) (done : ℕ) : Stack → List Bool :=
  bank source (fun k => (![
    [],
    if 0 < done then encodeNat (decodeNat (rawField source 0)) else [],
    if 1 < done then encodeNat (decodeNat (rawField source 1)) else [],
    if 2 < done then encodeNat (decodeNat (rawField source 2)) else [],
    if 3 < done then encodeNat (decodeNat (rawField source 3)) else [],
    [], [], [], [], []] : Fin 10 → List Bool) k)

@[simp] theorem prepared_zero (source : RequestParser.Stack → List Bool) :
    prepared source 0 = bank source (fun _ => []) := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

@[simp] theorem prepared_field (source : RequestParser.Stack → List Bool)
    (done : ℕ) (i : Fin 4) : prepared source done (field i) = rawField source i := rfl

@[simp] theorem prepared_extra_zero (source : RequestParser.Stack → List Bool) (done : ℕ) :
    prepared source done (extra 0) = [] := rfl

@[simp] theorem prepared_extra_eight (source : RequestParser.Stack → List Bool) (done : ℕ) :
    prepared source done (extra 8) = [] := rfl

theorem prepared_next_empty (source : RequestParser.Stack → List Bool) (i : Fin 4) :
    prepared source i.val (canonical i) = [] := by
  fin_cases i <;> rfl

theorem prepared_update (source : RequestParser.Stack → List Bool) (i : Fin 4) :
    Function.update (prepared source i.val) (canonical i)
      (encodeNat (decodeNat (rawField source i))) = prepared source (i.val + 1) := by
  funext k
  cases k with
  | inl k =>
      fin_cases i <;> simp only [Function.update_apply]
      all_goals rfl
  | inr k =>
      fin_cases i <;> fin_cases k <;> rfl

/-- Reuse the exact source word run in an arbitrary existing caller frame.
Only the selected canonical destination is updated; the original is preserved. -/
theorem prepare_into (i : Fin 4) (memory : Memory) (frame : Stack → List Bool)
    (hzero : frame (extra 0) = []) (hcanonical : frame (canonical i) = [])
    (hscratch : frame (extra 8) = []) :
    RunsExactly computer.step (cfg (wordLabel i 0) memory frame)
      (cfg (afterWord i) memory
        (Function.update frame (canonical i) (encodeNat (decodeNat (frame (field i))))))
      (4 * (frame (field i)).length + 5) := by
  have ez : Function.update frame (extra 0) [] = frame := by
    simpa only [hzero] using Function.update_eq_self (extra 0) frame
  have ec : Function.update frame (canonical i) [] = frame := by
    simpa only [hcanonical] using Function.update_eq_self (canonical i) frame
  have es : Function.update frame (extra 8) [] = frame := by
    simpa only [hscratch] using Function.update_eq_self (extra 8) frame
  have first : ParameterWords.tapes (wordMap i) frame (frame (field i)) [] [] [] = frame := by
    change Function.update (Function.update (Function.update
      (Function.update frame (field i) (frame (field i))) (extra 0) [])
      (canonical i) []) (extra 8) [] = frame
    rw [Function.update_eq_self, ez, ec, es]
  have last : ParameterWords.tapes (wordMap i) frame (frame (field i)) []
      (encodeNat (decodeNat (frame (field i)))) [] =
      Function.update frame (canonical i) (encodeNat (decodeNat (frame (field i)))) := by
    change Function.update (Function.update (Function.update
      (Function.update frame (field i) (frame (field i))) (extra 0) [])
      (canonical i) (encodeNat (decodeNat (frame (field i))))) (extra 8) [] = _
    rw [Function.update_eq_self, ez]
    have hne : canonical i ≠ extra 8 := by
      intro h
      have h' := congrArg (fun k : Stack => match k with | .inl _ => 100 | .inr n => n.val) h
      change i.val + 1 = 8 at h'
      omega
    rw [Function.update_comm hne, es]
  simpa only [first, last] using word_run i memory frame (frame (field i))

/-- A canonicalization step consumes the actual field produced by the parser. -/
theorem prepare_next (source : RequestParser.Stack → List Bool) (i : Fin 4) (memory : Memory) :
    RunsExactly computer.step
      (cfg (wordLabel i 0) memory (prepared source i.val))
      (cfg (afterWord i) memory (prepared source (i.val + 1)))
      (4 * (rawField source i).length + 5) := by
  simpa only [prepared_field, prepared_update] using
    prepare_into i memory (prepared source i.val) (prepared_extra_zero source i.val)
      (prepared_next_empty source i) (prepared_extra_eight source i.val)

/-- All four retained raw fields are physically copied and canonicalized in
this one program, in its actual order, with exact aggregate transition count. -/
theorem prepare_four (source : RequestParser.Stack → List Bool) (memory : Memory) :
    RunsExactly computer.step
      (cfg (wordLabel 0 0) memory (bank source (fun _ => [])))
      (cfg (ParameterProgram.control 3) memory (prepared source 4))
      (4 * ((rawField source 0).length + (rawField source 1).length +
        (rawField source 2).length + (rawField source 3).length) + 20) := by
  have h0 := prepare_next source 0 memory
  have h1 := prepare_next source 1 memory
  have h2 := prepare_next source 2 memory
  have h3 := prepare_next source 3 memory
  change RunsExactly computer.step (cfg (wordLabel 0 0) memory (prepared source 0))
    (cfg (wordLabel 1 0) memory (prepared source 1)) _ at h0
  rw [prepared_zero] at h0
  change RunsExactly computer.step _ (cfg (wordLabel 2 0) memory (prepared source 2)) _ at h1
  change RunsExactly computer.step _ (cfg (wordLabel 3 0) memory (prepared source 3)) _ at h2
  change RunsExactly computer.step _ (cfg (ParameterProgram.control 3) memory (prepared source 4)) _ at h3
  convert ((h0.trans h1).trans h2).trans h3 using 1 <;> omega

/-- Canonical words grow by at most the one explicit leading marker bit. -/
theorem canonical_length_le (raw : List Bool) :
    (encodeNat (decodeNat raw)).length ≤ raw.length + 1 := by
  rw [← NaturalWords.canonicalize_eq]
  exact (NaturalWords.canonicalize_length raw).2

/-- The actual comparator operand ordering: epsilon denominator/magnitude,
then delta magnitude/denominator. -/
def operandIndex (strict right : Bool) : Fin 4 :=
  if strict then (if right then 3 else 2) else (if right then 0 else 1)

def operandDestination (right : Bool) : Stack := extra (if right then 6 else 5)
def copyStart (strict right : Bool) : Label :=
  ParameterProgram.control (if strict then (if right then 10 else 8) else (if right then 5 else 3))
def copyRestore (strict right : Bool) : Label :=
  ParameterProgram.control (if strict then (if right then 11 else 9) else (if right then 6 else 4))
def copyNext (strict right : Bool) : Label :=
  if right then compareLabel strict () else copyStart strict true

/-- The caller performs both passes of the retained-operand copy. Its charge
is separate from the H1 prepared-comparator charge. -/
theorem copy_operand (strict right : Bool) (memory : Memory) (frame : Stack → List Bool)
    (hscratch : frame (extra 8) = [])
    (hdestination : frame (operandDestination right) = []) :
    RunsExactly computer.step (cfg (copyStart strict right) memory frame)
      (cfg (copyNext strict right) memory
        (Function.update frame (operandDestination right)
          (frame (canonical (operandIndex strict right)))))
      (2 * ((frame (canonical (operandIndex strict right))).length + 1)) := by
  have hsd : canonical (operandIndex strict right) ≠ operandDestination right := by
    cases strict <;> cases right <;> decide
  have hst : canonical (operandIndex strict right) ≠ extra 8 := by
    cases strict <;> cases right <;> decide
  have hdt : operandDestination right ≠ extra 8 := by cases right <;> decide
  have hm : ExecutesAt computer.step (copyStart strict right)
      (copyMoveStmt (canonical (operandIndex strict right)) (extra 8)
        (copyStart strict right) (copyRestore strict right)) := by
    cases strict <;> cases right <;> intro state tapes <;> rfl
  have hr : ExecutesAt computer.step (copyRestore strict right)
      (copyRestoreStmt (canonical (operandIndex strict right)) (operandDestination right)
        (extra 8) (copyRestore strict right) (copyNext strict right)) := by
    cases strict <;> cases right <;> intro state tapes <;> rfl
  simpa only [hdestination, List.append_nil] using
    copy_exact (canonical (operandIndex strict right)) (operandDestination right) (extra 8)
      hsd hst hdt computer.step (copyStart strict right) (copyRestore strict right)
      (copyNext strict right) hm hr memory frame hscratch

def canonicalWord (source : RequestParser.Stack → List Bool) (strict right : Bool) : List Bool :=
  encodeNat (decodeNat (rawField source (operandIndex strict right)))

@[simp] theorem prepared_canonical (source : RequestParser.Stack → List Bool) (i : Fin 4) :
    prepared source 4 (canonical i) = encodeNat (decodeNat (rawField source i)) := by
  fin_cases i <;> rfl

/-- Both physical copies and the actual comparator are executed in sequence.
The result bit is the only remaining temporary; all four canonical operands
and every original parser stack are preserved. -/
theorem compare_prepared (source : RequestParser.Stack → List Bool) (strict flag : Bool) :
    RunsExactly computer.step
      (cfg (copyStart strict false) (flag, BinaryArithmetic.Comparison.initial) (prepared source 4))
      (cfg (returnCompare strict) (flag, BinaryArithmetic.Comparison.initial)
        (Function.update (prepared source 4) (extra 7)
          [decide (decodeNat (rawField source (operandIndex strict false)) <
            decodeNat (rawField source (operandIndex strict true)))]))
      (2 * ((canonicalWord source strict false).length + 1) +
       2 * ((canonicalWord source strict true).length + 1) +
       max (canonicalWord source strict false).length (canonicalWord source strict true).length + 1) := by
  let a := canonicalWord source strict false
  let b := canonicalWord source strict true
  let first := Function.update (prepared source 4) (extra 5) a
  let second := Function.update first (extra 6) b
  have h1 := copy_operand strict false (flag, BinaryArithmetic.Comparison.initial)
    (prepared source 4) rfl rfl
  change RunsExactly computer.step _ (cfg (copyStart strict true) _
    (Function.update (prepared source 4) (extra 5)
      (prepared source 4 (canonical (operandIndex strict false))))) _ at h1
  simp only [prepared_canonical] at h1
  have hscratch : first (extra 8) = [] := rfl
  have hdest : first (operandDestination true) = [] := rfl
  have hc : first (canonical (operandIndex strict true)) = b := by
    cases strict <;> rfl
  have h2 := copy_operand strict true (flag, BinaryArithmetic.Comparison.initial)
    first hscratch hdest
  rw [hc] at h2
  have before : comparisonTapes (prepared source 4) a b [] = second := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  have after (answer : Bool) : comparisonTapes (prepared source 4) [] [] [answer] =
      Function.update (prepared source 4) (extra 7) [answer] := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  have h3 := comparison_run strict flag (prepared source 4)
    (decodeNat (rawField source (operandIndex strict false)))
    (decodeNat (rawField source (operandIndex strict true)))
  change RunsExactly computer.step
    (cfg (compareLabel strict ()) _ (comparisonTapes (prepared source 4) a b []))
    (cfg (returnCompare strict) _ (comparisonTapes (prepared source 4) [] [] _))
    (max a.length b.length + 1) at h3
  rw [before, after] at h3
  convert (h1.trans h2).trans h3 using 1 <;> dsimp only [a, b, canonicalWord] <;> omega

/-- Final configurations use the existing program's physical status register. -/
def finished (status : Bool) (tapes : Stack → List Bool) : Config :=
  ⟨none, (none, status, BinaryArithmetic.Comparison.initial), tapes⟩

theorem halt_step (status : Bool) (state : State) (tapes : Stack → List Bool) :
    computer.step ⟨some (ParameterProgram.control (if status then 13 else 14)), state, tapes⟩ =
      some (finished status tapes) := by cases status <;> rfl

theorem dispatch_step (status : Bool) (source : RequestParser.Stack → List Bool) :
    computer.step (cfg (ParameterProgram.control 0) (status, BinaryArithmetic.Comparison.initial)
      (bank source (fun _ => []))) =
      some (cfg (ParameterProgram.control (if status then 1 else 14))
        (status, BinaryArithmetic.Comparison.initial) (bank source (fun _ => []))) := by
  cases status <;> rfl

/-- A failed original parser takes exactly the dispatch and failure-halt steps. -/
theorem reject_parser (source : RequestParser.Stack → List Bool) :
    RunsExactly computer.step
      (cfg (ParameterProgram.control 0) (false, BinaryArithmetic.Comparison.initial) (bank source (fun _ => [])))
      (finished false (bank source (fun _ => []))) 2 := by
  exact (runsExactly_one (dispatch_step false source)).trans
    (runsExactly_one (halt_step false (none, false, BinaryArithmetic.Comparison.initial) _))

/-- The successful parser bank agrees with these exact retained raw fields. -/
def SourceFields (source : RequestParser.Stack → List Bool) (f : ProblemHeader.Fields) : Prop :=
  ∀ k, source (RequestParser.headerMap k) = RequestParser.outputTapes f k

theorem rawField_eq {source : RequestParser.Stack → List Bool} {f : ProblemHeader.Fields}
    (h : SourceFields source f) (i : Fin 4) :
    rawField source i = (![f.epsilon.magnitude, f.epsilon.denominator,
      f.delta.magnitude, f.delta.denominator] : Fin 4 → List Bool) i := by
  fin_cases i
  · exact h (.inl 5)
  · exact h (.inl 2)
  · exact h (.inl 7)
  · exact h (.inl 3)

def rationalField (f : ProblemHeader.Fields) (delta : Bool) : RationalFields.Fields :=
  if delta then f.delta else f.epsilon

theorem bank_sign {source : RequestParser.Stack → List Bool} {f : ProblemHeader.Fields}
    (h : SourceFields source f) (delta : Bool) :
    bank source (fun _ => []) (sign delta) = [(rationalField f delta).negative] := by
  cases delta
  · exact h (.inl 6)
  · exact h (.inl 8)

theorem bank_magnitude {source : RequestParser.Stack → List Bool} {f : ProblemHeader.Fields}
    (h : SourceFields source f) (delta : Bool) :
    bank source (fun _ => []) (field (if delta then 2 else 0)) =
      (rationalField f delta).magnitude := by
  cases delta
  · exact h (.inl 5)
  · exact h (.inl 7)

theorem positive_exec (delta : Bool) :
    ExecutesAt computer.step (ParameterProgram.control (if delta then 2 else 1))
      (positiveStmt delta (if delta then wordLabel 0 0 else ParameterProgram.control 2)) := by
  cases delta <;> intro state tape <;> rfl

/-- A physical sign peek and a physical nonempty-magnitude peek continue in
one transition when the raw unsigned-positive predicate holds. -/
theorem positive_step (delta : Bool) (memory : Memory) (frame : Stack → List Bool)
    (f : RationalFields.Fields) (hs : frame (sign delta) = [f.negative])
    (hm : frame (field (if delta then 2 else 0)) = f.magnitude)
    (hu : ParameterSemantics.unsigned f) :
    computer.step (cfg (ParameterProgram.control (if delta then 2 else 1)) memory frame) =
      some (cfg (if delta then wordLabel 0 0 else ParameterProgram.control 2) memory frame) := by
  rcases hu with ⟨hn, hne⟩
  cases hw : f.magnitude with
  | nil => exact False.elim (hne hw)
  | cons b rest =>
    change computer.step ⟨some (ParameterProgram.control (if delta then 2 else 1)), (none, memory), frame⟩ = _
    rw [positive_exec delta]
    simp [positiveStmt, TM2.stepAux, hs, hn, hm, hw, cfg]
    rfl

/-- Rejection of either physical sign/zero check includes the actual failure
halt; scratch-register residues are discarded by that existing halt statement. -/
theorem positive_reject (delta : Bool) (memory : Memory) (frame : Stack → List Bool)
    (f : RationalFields.Fields) (hs : frame (sign delta) = [f.negative])
    (hm : frame (field (if delta then 2 else 0)) = f.magnitude)
    (hu : ¬ ParameterSemantics.unsigned f) :
    RunsExactly computer.step (cfg (ParameterProgram.control (if delta then 2 else 1)) memory frame)
      (finished false frame) 2 := by
  cases hn : f.negative with
  | true =>
    have step : computer.step (cfg (ParameterProgram.control (if delta then 2 else 1)) memory frame) =
        some (⟨some (ParameterProgram.control 14), (some true, memory), frame⟩ : Config) := by
      change computer.step ⟨some (ParameterProgram.control (if delta then 2 else 1)), (none, memory), frame⟩ = _
      rw [positive_exec delta]
      simp [positiveStmt, TM2.stepAux, hs, hn]
      rfl
    exact (runsExactly_one step).trans (runsExactly_one (halt_step false _ _))
  | false =>
    have hz : f.magnitude = [] := by
      by_contra hne
      exact hu ⟨hn, hne⟩
    have step : computer.step (cfg (ParameterProgram.control (if delta then 2 else 1)) memory frame) =
        some (cfg (ParameterProgram.control 14) memory frame) := by
      change computer.step ⟨some (ParameterProgram.control (if delta then 2 else 1)), (none, memory), frame⟩ = _
      rw [positive_exec delta]
      simp [positiveStmt, TM2.stepAux, hs, hn, hm, hz, cfg]
      rfl
    exact (runsExactly_one step).trans (runsExactly_one (halt_step false _ _))

theorem answer_clear (source : RequestParser.Stack → List Bool) (b : Bool) :
    Function.update (Function.update (prepared source 4) (extra 7) [b]) (extra 7) [] =
      prepared source 4 := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

/-- The returned one-bit answer is physically popped, and the caller proceeds
with a clean optional-bit register on its accepting branch. -/
theorem answer_continue (source : RequestParser.Stack → List Bool) (memory : Memory)
    (strict : Bool) :
    computer.step (cfg (returnCompare strict) memory
      (Function.update (prepared source 4) (extra 7) [strict])) =
      some (cfg (ParameterProgram.control (if strict then 13 else 8)) memory (prepared source 4)) := by
  cases strict <;>
    change some (cfg _ memory
      (Function.update (Function.update (prepared source 4) (extra 7) [_]) (extra 7) [])) = _
  all_goals rw [answer_clear]
  all_goals rfl

/-- The rejecting answer branch consumes its bit and executes the existing
failure halt. Thus no comparator operands, answer, or scratch remain. -/
theorem answer_reject (source : RequestParser.Stack → List Bool) (memory : Memory)
    (strict : Bool) :
    RunsExactly computer.step
      (cfg (returnCompare strict) memory
        (Function.update (prepared source 4) (extra 7) [!strict]))
      (finished false (prepared source 4)) 2 := by
  have step : computer.step (cfg (returnCompare strict) memory
        (Function.update (prepared source 4) (extra 7) [!strict])) =
      some (⟨some (ParameterProgram.control 14), (some (!strict), memory), prepared source 4⟩ : Config) := by
    cases strict <;>
      change some (⟨some (ParameterProgram.control 14), (some _, memory),
        Function.update (Function.update (prepared source 4) (extra 7) [_])
          (extra 7) []⟩ : Config) = _
    all_goals rw [answer_clear]
  exact (runsExactly_one step).trans (runsExactly_one (halt_step false _ _))

def comparisonTime (source : RequestParser.Stack → List Bool) (strict : Bool) : ℕ :=
  2 * ((canonicalWord source strict false).length + 1) +
  2 * ((canonicalWord source strict true).length + 1) +
  max (canonicalWord source strict false).length (canonicalWord source strict true).length + 1

/-- This Boolean describes only the comparisons; positivity was checked by
physical peeks before the canonicalization calls. -/
def comparisonResult (source : RequestParser.Stack → List Bool) : Bool :=
  (!decide (decodeNat (rawField source 1) < decodeNat (rawField source 0))) &&
    decide (decodeNat (rawField source 2) < decodeNat (rawField source 3))

/-- Both comparisons, their dispatches, and the actual good/bad halt execute
on the canonicalized bank. The failure of epsilon short-circuits delta. -/
theorem comparisons (source : RequestParser.Stack → List Bool) :
    ∃ time, time ≤ comparisonTime source false + comparisonTime source true + 3 ∧
      RunsExactly computer.step
        (cfg (ParameterProgram.control 3) (true, BinaryArithmetic.Comparison.initial) (prepared source 4))
        (finished (comparisonResult source) (prepared source 4)) time := by
  have he := compare_prepared source false true
  change RunsExactly computer.step
    (cfg (ParameterProgram.control 3) (true, BinaryArithmetic.Comparison.initial) (prepared source 4))
    (cfg (ParameterProgram.control 7) (true, BinaryArithmetic.Comparison.initial)
      (Function.update (prepared source 4) (extra 7)
        [decide (decodeNat (rawField source 1) < decodeNat (rawField source 0))]))
    (comparisonTime source false) at he
  cases heq : decide (decodeNat (rawField source 1) < decodeNat (rawField source 0)) with
  | true =>
    rw [heq] at he
    have hr := he.trans (answer_reject source (true, BinaryArithmetic.Comparison.initial) false)
    refine ⟨2 + comparisonTime source false, by omega, ?_⟩
    simpa only [comparisonResult, heq, Bool.not_true, Bool.false_and] using hr
  | false =>
    rw [heq] at he
    have first := he.trans
      (runsExactly_one (answer_continue source (true, BinaryArithmetic.Comparison.initial) false))
    have hd := compare_prepared source true true
    change RunsExactly computer.step
      (cfg (ParameterProgram.control 8) (true, BinaryArithmetic.Comparison.initial) (prepared source 4))
      (cfg (ParameterProgram.control 12) (true, BinaryArithmetic.Comparison.initial)
        (Function.update (prepared source 4) (extra 7)
          [decide (decodeNat (rawField source 2) < decodeNat (rawField source 3))]))
      (comparisonTime source true) at hd
    cases hdq : decide (decodeNat (rawField source 2) < decodeNat (rawField source 3)) with
    | false =>
      rw [hdq] at hd
      have hr := (first.trans hd).trans
        (answer_reject source (true, BinaryArithmetic.Comparison.initial) true)
      refine ⟨2 + (comparisonTime source true + (1 + comparisonTime source false)), by omega, ?_⟩
      simpa only [comparisonResult, heq, hdq, Bool.not_false, Bool.true_and] using hr
    | true =>
      rw [hdq] at hd
      have hr := ((first.trans hd).trans
        (runsExactly_one (answer_continue source (true, BinaryArithmetic.Comparison.initial) true))).trans
        (runsExactly_one (halt_step true (none, true, BinaryArithmetic.Comparison.initial) _))
      refine ⟨1 + (1 + (comparisonTime source true + (1 + comparisonTime source false))), by omega, ?_⟩
      simpa only [comparisonResult, heq, hdq, Bool.not_false, Bool.true_and] using hr

/-- A physical word-length bound controls the actual copy/comparator time.
Decoded numeric values do not ParameterProgram.control an iteration count. -/
theorem comparisonTime_le (source : RequestParser.Stack → List Bool) (strict : Bool) (n : ℕ)
    (hl : ∀ i, (rawField source i).length ≤ n) : comparisonTime source strict ≤ 5 * n + 10 := by
  have ha := canonical_length_le (rawField source (operandIndex strict false))
  have hb := canonical_length_le (rawField source (operandIndex strict true))
  have hla := hl (operandIndex strict false)
  have hlb := hl (operandIndex strict true)
  have ham : (canonicalWord source strict false).length ≤ n + 1 := by
    unfold canonicalWord; omega
  have hbm : (canonicalWord source strict true).length ≤ n + 1 := by
    unfold canonicalWord; omega
  have hm := max_le ham hbm
  unfold comparisonTime
  omega

/-- Canonicalization and both comparisons are one run of the existing machine. -/
theorem prepared_validation (source : RequestParser.Stack → List Bool) (n : ℕ)
    (hl : ∀ i, (rawField source i).length ≤ n) :
    ∃ time, time ≤ 26 * n + 43 ∧
      RunsExactly computer.step
        (cfg (wordLabel 0 0) (true, BinaryArithmetic.Comparison.initial) (bank source (fun _ => [])))
        (finished (comparisonResult source) (prepared source 4)) time := by
  obtain ⟨time, ht, hr⟩ := comparisons source
  have hp := prepare_four source (true, BinaryArithmetic.Comparison.initial)
  refine ⟨time + (4 * ((rawField source 0).length + (rawField source 1).length +
      (rawField source 2).length + (rawField source 3).length) + 20), ?_, hp.trans hr⟩
  have ht0 := comparisonTime_le source false n hl
  have ht1 := comparisonTime_le source true n hl
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  have h3 := hl 3
  omega

/-- On genuinely positive parsed rationals, the two computed bits are exactly
the original request's remaining accuracy/confidence validity condition. -/
theorem comparisonResult_eq {source : RequestParser.Stack → List Bool} {f : ProblemHeader.Fields}
    (hs : SourceFields source f) (he : f.epsilon.denominator ≠ []) (hd : f.delta.denominator ≠ [])
    (hue : ParameterSemantics.unsigned f.epsilon) (hud : ParameterSemantics.unsigned f.delta) :
    comparisonResult source =
      decide (Program.ValidRequest (RationalFields.value f.epsilon) (RationalFields.value f.delta)) := by
  unfold comparisonResult
  rw [rawField_eq hs 0, rawField_eq hs 1, rawField_eq hs 2, rawField_eq hs 3]
  change ((!decide (decodeNat f.epsilon.denominator < decodeNat f.epsilon.magnitude)) &&
    decide (decodeNat f.delta.magnitude < decodeNat f.delta.denominator)) = _
  rw [← decide_not, ← Bool.decide_and]
  congr 1
  apply propext
  rw [ParameterSemantics.validRequest_iff _ _ he hd]
  simp only [ParameterSemantics.epsilonValid, ParameterSemantics.deltaValid, hue, hud, true_and]
  omega

/-- Every successfully separated rational uses a nonempty denominator, and
all four retained words are bounded by the actual complete raw input length. -/
theorem parsed_parameter_bounds {raw : List Bool} {f : ProblemHeader.Fields}
    (h : ProblemHeader.separate raw = some f) :
    f.epsilon.denominator ≠ [] ∧ f.delta.denominator ≠ [] ∧
      f.epsilon.magnitude.length ≤ raw.length ∧ f.epsilon.denominator.length ≤ raw.length ∧
      f.delta.magnitude.length ≤ raw.length ∧ f.delta.denominator.length ≤ raw.length := by
  cases hp : Preamble.separate raw with
  | none => simp [ProblemHeader.separate, hp] at h
  | some p =>
    cases hv : Encoding.unframe p.problem with
    | none => simp [ProblemHeader.separate, hp, hv] at h
    | some pair =>
      rcases pair with ⟨word, body⟩
      simp [ProblemHeader.separate, hp, hv] at h
      subst f
      unfold Preamble.separate at hp
      cases ho : Contract.split raw with
      | none => simp [ho] at hp
      | some outer =>
        cases he : RationalFields.separate outer.epsilon with
        | none => simp [ho, he] at hp
        | some e =>
          cases hd : RationalFields.separate outer.delta with
          | none => simp [ho, he, hd] at hp
          | some d =>
            simp [ho, he, hd] at hp
            subst p
            have houter := Contract.split_length ho
            obtain ⟨heraw, heden⟩ := RationalFields.separate_some he
            obtain ⟨hdraw, hdden⟩ := RationalFields.separate_some hd
            have helen := congrArg List.length heraw
            have hdlen := congrArg List.length hdraw
            simp only [RationalFields.join, List.length_append, Encoding.frame_length,
              List.length_singleton] at helen hdlen
            refine ⟨heden, hdden, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega

/-- A semantic success of the unchanged raw decoder identifies the exact
retained rational fields; it does not require canonical codewords. -/
theorem decoded_fields {raw : List Bool} {r : ProgramEncoding.Request}
    (h : ProgramEncoding.request.decode raw = some r) :
    ∃ f : ProblemHeader.Fields, ProblemHeader.separate raw = some f ∧
      r.epsilon = RationalFields.value f.epsilon ∧ r.delta = RationalFields.value f.delta := by
  have hx := ProblemHeader.decode_eq raw
  rw [h] at hx
  cases hs : ProblemHeader.separate raw with
  | none => simp [hs] at hx
  | some f =>
    simp only [hs, Option.bind_some] at hx
    cases hf : (Encoding.formula f.variableWord.length).decode f.formula with
    | none => simp [ProblemHeader.validate, hf] at hx
    | some formula =>
      simp [ProblemHeader.validate, hf] at hx
      subst r
      exact ⟨f, rfl, rfl, rfl⟩

/-- Complete sign, zero, canonicalization and comparison suffix for a parser
bank. Rejecting sign/zero branches halt before any operand normalization. -/
theorem validate_fields {source : RequestParser.Stack → List Bool} {f : ProblemHeader.Fields}
    (hs : SourceFields source f) (he : f.epsilon.denominator ≠ []) (hd : f.delta.denominator ≠ [])
    (n : ℕ) (hl : ∀ i, (rawField source i).length ≤ n) :
    ∃ ending time, time ≤ 26 * n + 45 ∧
      RunsExactly computer.step
        (cfg (ParameterProgram.control 1) (true, BinaryArithmetic.Comparison.initial)
          (bank source (fun _ => [])))
        (finished (decide (Program.ValidRequest (RationalFields.value f.epsilon)
          (RationalFields.value f.delta))) ending) time ∧
      (Program.ValidRequest (RationalFields.value f.epsilon) (RationalFields.value f.delta) →
        ending = prepared source 4) := by
  let memory : Memory := (true, BinaryArithmetic.Comparison.initial)
  let frame := bank source (fun _ => [])
  by_cases hue : ParameterSemantics.unsigned f.epsilon
  · have pe := runsExactly_one (positive_step false memory frame f.epsilon
      (bank_sign hs false) (bank_magnitude hs false) hue)
    by_cases hud : ParameterSemantics.unsigned f.delta
    · have pd := runsExactly_one (positive_step true memory frame f.delta
        (bank_sign hs true) (bank_magnitude hs true) hud)
      obtain ⟨time, ht, hr⟩ := prepared_validation source n hl
      rw [comparisonResult_eq hs he hd hue hud] at hr
      exact ⟨prepared source 4, time + 2, by omega, (pe.trans pd).trans hr, fun _ => rfl⟩
    · have invalid : ¬ Program.ValidRequest (RationalFields.value f.epsilon)
          (RationalFields.value f.delta) := by
        intro hv
        exact hud ((ParameterSemantics.validRequest_iff _ _ he hd).mp hv).2.1
      have hr := pe.trans (positive_reject true memory frame f.delta
        (bank_sign hs true) (bank_magnitude hs true) hud)
      refine ⟨frame, 3, by omega, ?_, fun hv => False.elim (invalid hv)⟩
      simp only [invalid, decide_false]
      convert hr using 1 <;> rfl
  · have invalid : ¬ Program.ValidRequest (RationalFields.value f.epsilon)
        (RationalFields.value f.delta) := by
      intro hv
      exact hue ((ParameterSemantics.validRequest_iff _ _ he hd).mp hv).1.1
    have hr := positive_reject false memory frame f.epsilon
      (bank_sign hs false) (bank_magnitude hs false) hue
    refine ⟨frame, 2, by omega, ?_, fun hv => False.elim (invalid hv)⟩
    simp only [invalid, decide_false]
    convert hr using 1 <;> rfl

/-- Conservative physical-input polynomial for the existing complete parameter
validator, including the unchanged full request parser. -/
def timeBound (n : ℕ) : ℕ := RequestParser.timeBound n + 40 * n + 100

/-- All raw inputs halt with exactly the original decoder-and-validity result.
A successful run preserves the original parser fields and installs exactly
four canonical operands, leaving every other work stack empty. -/
theorem terminates (raw : List Bool) :
    ∃ ending time, time ≤ timeBound raw.length ∧
      RunsExactly computer.step (initList computer raw)
        (finished ((ProgramEncoding.request.decode raw).any
          (fun r => decide (Program.ValidRequest r.epsilon r.delta))) ending) time ∧
      (∀ r, ProgramEncoding.request.decode raw = some r → Program.ValidRequest r.epsilon r.delta →
        ∃ source f, SourceFields source f ∧ ProblemHeader.separate raw = some f ∧
          ending = prepared source 4) := by
  obtain ⟨source, time, ht, hr, keep⟩ := parser_run raw
  cases hdecode : ProgramEncoding.request.decode raw with
  | none =>
    rw [hdecode] at hr
    have run := hr.trans (reject_parser source)
    refine ⟨bank source (fun _ => []), 2 + time, ?_, run, ?_⟩
    · unfold timeBound; omega
    · intro r hd _; simp only [hdecode, reduceCtorEq] at hd
  | some r =>
    rw [hdecode] at hr
    obtain ⟨f, hf, heq, hdq⟩ := decoded_fields hdecode
    have hs : SourceFields source f := keep f hf
    obtain ⟨he, hd, h0, h1, h2, h3⟩ := parsed_parameter_bounds hf
    have hl : ∀ i, (rawField source i).length ≤ raw.length := by
      intro i
      rw [rawField_eq hs i]
      fin_cases i <;> assumption
    obtain ⟨ending, rest, hb, tail, success⟩ := validate_fields hs he hd raw.length hl
    have first := hr.trans (runsExactly_one (dispatch_step true source))
    have run := first.trans tail
    refine ⟨ending, rest + (1 + time), ?_, ?_, ?_⟩
    · unfold timeBound; omega
    · simpa only [hdecode, Option.any_some, heq, hdq] using run
    · intro r' hr' hv
      have rr : r' = r := (Option.some.inj hr').symm
      subst r'
      rw [heq, hdq] at hv
      exact ⟨source, f, hs, hf, success hv⟩

/-- The very same concrete run accumulates canonical primitive instruction
cost. No arithmetic operation or raw-field decoder is charged as one step. -/
theorem bit_cost (raw : List Bool) :
    ∃ ending time, time ≤ timeBound raw.length ∧
      (Primitive.run program time (some (initList computer raw))).2 =
        some (finished ((ProgramEncoding.request.decode raw).any
          (fun r => decide (Program.ValidRequest r.epsilon r.delta))) ending) ∧
      (Primitive.run program time (some (initList computer raw))).1 ≤ 10 * timeBound raw.length := by
  obtain ⟨ending, time, ht, hr, _⟩ := terminates raw
  obtain ⟨hc, cost⟩ := Primitive.execution_cost program 10 statement_budget time _ _ hr
  exact ⟨ending, time, ht, hc, cost.trans (Nat.mul_le_mul_left 10 ht)⟩

end Counting.Algorithm.KarpLubyRequest.ParameterValidation




