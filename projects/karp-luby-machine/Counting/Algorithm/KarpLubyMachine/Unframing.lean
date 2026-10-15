import Counting.Algorithm.KarpLubyMachine.Framing

/-!
# Finite-stack parsing of the existing framing codec

This is an actual TM2 parser for `KarpLuby.Encoding.unframe`. On success it
leaves the unconsumed suffix on the input stack and the decoded word on the
output stack. On malformed input it empties the scratch stack and signals
failure. A finite Boolean register records success; no list, natural number,
or parsed value is stored in finite control.

The interface deliberately exposes the complete multistack terminal
configuration. A later caller may consume the decoded word and continue
parsing the suffix. This is not yet an F1 single-output serialization witness
for `Option (Bits × Bits)`.

The explicit-configuration proof technique is reused from the sibling
`Framing` module, originally adapted from F1's
`Counting/Examples/Machines.lean`. The parsing equations and codec are
imported from the unique R1 `Encoding` provider.
-/

namespace Counting.Algorithm.KarpLubyMachine

open Turing Computability
open Turing.TM2.Stmt

namespace Unframing

open KarpLuby

/-- Four labels: marker, data, reverse, and error cleanup. -/
abbrev marker : Bool × Bool := (false, false)
abbrev dataBit : Bool × Bool := (false, true)
abbrev reverse : Bool × Bool := (true, false)
abbrev clear : Bool × Bool := (true, true)

/-- Three binary stacks and a six-element finite register implement parsing.
The second register component records success at the final halt. -/
abbrev computer : FinTM2 where
  K := Option Bool
  k₀ := none
  k₁ := some true
  Γ _ := Bool
  Λ := Bool × Bool
  main := marker
  σ := Option Bool × Bool
  initialState := (none, false)
  m phase := if phase.1 then
    if phase.2 then
      pop (some false) (fun s x => (x, s.2))
        (branch (fun s => s.1.isSome)
          (load (fun _ => (none, false)) (goto (fun _ => clear)))
          (load (fun _ => (none, false)) halt))
    else
      pop (some false) (fun s x => (x, s.2))
        (branch (fun s => s.1.isSome)
          (push (some true) (fun s => s.1.getD false)
            (load (fun _ => (none, true)) (goto (fun _ => reverse))))
          (load (fun _ => (none, true)) halt))
    else
    if phase.2 then
      pop none (fun s x => (x, s.2))
        (branch (fun s => s.1.isSome)
          (push (some false) (fun s => s.1.getD false)
            (load (fun _ => (none, false)) (goto (fun _ => marker))))
          (load (fun _ => (none, false)) (goto (fun _ => clear))))
    else
      pop none (fun s x => (x, s.2))
        (branch (fun s => s.1.isSome)
          (branch (fun s => s.1.getD false)
            (load (fun _ => (none, false)) (goto (fun _ => dataBit)))
            (load (fun _ => (none, true)) (goto (fun _ => reverse))))
          (load (fun _ => (none, false)) (goto (fun _ => clear))))

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) :=
  inferInstanceAs (Fintype Bool)

/-- All stacks and the finite success register are explicit in the invariant. -/
def cfg (phase : Bool × Bool) (input scratch output : List Bool) : computer.Cfg where
  l := some phase
  var := (none, phase.1 && !phase.2)
  stk k := match k with
    | none => input
    | some false => scratch
    | some true => output

/-- Successful parsing returns two separate strings and a Boolean status.
Failed parsing has empty strings and a false status. Scratch is always empty. -/
def done (success : Bool) (word rest : List Bool) : computer.Cfg where
  l := none
  var := (none, success)
  stk k := match k with
    | none => rest
    | some false => []
    | some true => word

@[simp] theorem cfg_init (input : List Bool) :
    cfg marker input [] [] = initList computer input := by
  unfold cfg initList
  congr 1
  funext k
  rcases k with _ | (_ | _) <;> rfl

@[simp] theorem step_done (success : Bool) (word rest : List Bool) :
    computer.step (done success word rest) = none := rfl

@[simp] theorem step_marker_nil (scratch : List Bool) :
    computer.step (cfg marker [] scratch []) = some (cfg clear [] scratch []) := by
  simp [FinTM2.step, TM2.step, computer, cfg, TM2.stepAux]
  congr 2

@[simp] theorem step_marker_false (rest scratch : List Bool) :
    computer.step (cfg marker (false :: rest) scratch []) =
      some (cfg reverse rest scratch []) := by
  simp [FinTM2.step, TM2.step, computer, cfg, TM2.stepAux]
  congr 2
  funext k
  rcases k with _ | (_ | _) <;> simp

@[simp] theorem step_marker_true (rest scratch : List Bool) :
    computer.step (cfg marker (true :: rest) scratch []) =
      some (cfg dataBit rest scratch []) := by
  simp [FinTM2.step, TM2.step, computer, cfg, TM2.stepAux]
  congr 2
  funext k
  rcases k with _ | (_ | _) <;> simp

@[simp] theorem step_data_nil (scratch : List Bool) :
    computer.step (cfg dataBit [] scratch []) = some (cfg clear [] scratch []) := by
  simp [FinTM2.step, TM2.step, computer, cfg, TM2.stepAux]
  congr 2

@[simp] theorem step_data_cons (b : Bool) (rest scratch : List Bool) :
    computer.step (cfg dataBit (b :: rest) scratch []) =
      some (cfg marker rest (b :: scratch) []) := by
  simp [FinTM2.step, TM2.step, computer, cfg, TM2.stepAux]
  congr 2
  funext k
  rcases k with _ | (_ | _) <;> simp

@[simp] theorem step_reverse_nil (rest output : List Bool) :
    computer.step (cfg reverse rest [] output) = some (done true output rest) := by
  simp [FinTM2.step, TM2.step, computer, cfg, done, TM2.stepAux]
  congr 2

@[simp] theorem step_reverse_cons (b : Bool) (rest scratch output : List Bool) :
    computer.step (cfg reverse rest (b :: scratch) output) =
      some (cfg reverse rest scratch (b :: output)) := by
  simp [FinTM2.step, TM2.step, computer, cfg, TM2.stepAux]
  congr 2
  funext k
  rcases k with _ | (_ | _) <;> simp

@[simp] theorem step_clear_nil :
    computer.step (cfg clear [] [] []) = some (done false [] []) := by
  simp [FinTM2.step, TM2.step, computer, cfg, done, TM2.stepAux]
  congr 2

@[simp] theorem step_clear_cons (b : Bool) (scratch : List Bool) :
    computer.step (cfg clear [] (b :: scratch) []) = some (cfg clear [] scratch []) := by
  simp [FinTM2.step, TM2.step, computer, cfg, TM2.stepAux]
  congr 2
  funext k
  rcases k with _ | (_ | _) <;> simp

/-- A single actual machine transition followed by a fixed-length execution. -/
private theorem stepThen {a b c : computer.Cfg} {n : ℕ}
    (hab : computer.step a = some b)
    (hbc : (flip bind computer.step)^[n] (some b) = some c) :
    (flip bind computer.step)^[n + 1] (some a) = some c := by
  rw [Function.iterate_succ_apply]
  change (flip bind computer.step)^[n] (computer.step a) = some c
  rw [hab]
  exact hbc

/-- Reversing the accumulated payload preserves the remaining input suffix. -/
def reverseRun (rest scratch output : List Bool) :
    StateTransition.EvalsToInTime computer.step
      (cfg reverse rest scratch output)
      (some (done true (scratch.reverse ++ output) rest))
      (scratch.length + 1) where
  steps := scratch.length + 1
  evals_in_steps := by
    induction scratch generalizing output with
    | nil => exact step_reverse_nil rest output
    | cons b scratch ih =>
      have h := stepThen (step_reverse_cons b rest scratch output) (ih (b :: output))
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using h
  steps_le_m := Nat.le_refl _

/-- Malformed inputs erase the accumulated payload before the failure halt. -/
def clearRun (scratch : List Bool) :
    StateTransition.EvalsToInTime computer.step (cfg clear [] scratch [])
      (some (done false [] [])) (scratch.length + 1) where
  steps := scratch.length + 1
  evals_in_steps := by
    induction scratch with
    | nil => exact step_clear_nil
    | cons b scratch ih => exact stepThen (step_clear_cons b scratch) ih
  steps_le_m := Nat.le_refl _

/-- The exact execution length counts parsing and the final reverse/cleanup.
It stops at the first delimiter rather than traversing the remaining suffix. -/
def parseSteps : List Bool → ℕ
  | [] => 2
  | false :: _ => 2
  | [true] => 3
  | true :: _ :: rest => parseSteps rest + 3

/-- The mathematical parser specifies the complete final configuration. -/
def result (input scratch : List Bool) : computer.Cfg :=
  match Encoding.unframe input with
  | none => done false [] []
  | some (word, rest) => done true (scratch.reverse ++ word) rest

theorem result_pair (b : Bool) (rest scratch : List Bool) :
    result (true :: b :: rest) scratch = result rest (b :: scratch) := by
  cases h : Encoding.unframe rest with
  | none => simp [result, Encoding.unframe, h]
  | some p =>
    rcases p with ⟨word, tail⟩
    simp [result, Encoding.unframe, h, List.reverse_cons, List.append_assoc]

/-- Exact execution for every input, including both forms of premature EOF. -/
theorem parse_evals (input scratch : List Bool) :
    (flip bind computer.step)^[parseSteps input + scratch.length]
      (some (cfg marker input scratch [])) = some (result input scratch) := by
  match input with
  | [] =>
    have h := stepThen (step_marker_nil scratch) (clearRun scratch).evals_in_steps
    simpa [parseSteps, clearRun, result, Encoding.unframe, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using h
  | false :: rest =>
    have h := stepThen (step_marker_false rest scratch) (reverseRun rest scratch []).evals_in_steps
    simpa [parseSteps, reverseRun, result, Encoding.unframe, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using h
  | [true] =>
    have h := stepThen (step_marker_true [] scratch)
      (stepThen (step_data_nil scratch) (clearRun scratch).evals_in_steps)
    simpa [parseSteps, clearRun, result, Encoding.unframe, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using h
  | true :: b :: rest =>
    have h := stepThen (step_marker_true (b :: rest) scratch)
      (stepThen (step_data_cons b rest scratch) (parse_evals rest (b :: scratch)))
    rw [result_pair, show parseSteps (true :: b :: rest) + scratch.length =
      parseSteps rest + (b :: scratch).length + 1 + 1 by
        simp only [parseSteps, List.length_cons]; omega]
    exact h
termination_by input.length

theorem parseSteps_le (input : List Bool) : parseSteps input ≤ 2 * input.length + 2 := by
  match input with
  | [] => simp [parseSteps]
  | false :: rest => simp [parseSteps]
  | [true] => simp [parseSteps]
  | true :: b :: rest =>
    have ih := parseSteps_le rest
    simp only [parseSteps, List.length_cons]
    omega
termination_by input.length

@[simp] theorem parseSteps_frame_append (word rest : List Bool) :
    parseSteps (Encoding.frame word ++ rest) = 3 * word.length + 2 := by
  induction word with
  | nil => simp [Encoding.frame, parseSteps]
  | cons b word ih => simp [Encoding.frame, parseSteps, ih]; omega

/-- The auxiliary run makes the accumulator and the exact count available. -/
def parseRun (input scratch : List Bool) :
    StateTransition.EvalsToInTime computer.step (cfg marker input scratch [])
      (some (result input scratch)) (parseSteps input + scratch.length) where
  steps := parseSteps input + scratch.length
  evals_in_steps := parse_evals input scratch
  steps_le_m := Nat.le_refl _

/-- Every binary input terminates within the explicit linear transition bound. -/
def run (input : List Bool) :
    StateTransition.EvalsToInTime computer.step (initList computer input)
      (some (result input [])) (2 * input.length + 2) where
  steps := parseSteps input
  evals_in_steps := by
    simpa only [List.length_nil, Nat.add_zero, cfg_init] using parse_evals input []
  steps_le_m := parseSteps_le input

@[simp] theorem run_steps (input : List Bool) : (run input).steps = parseSteps input := rfl

/-- Successful parsing materializes the word and preserves the exact suffix. -/
def successRun (input word rest : List Bool)
    (h : Encoding.unframe input = some (word, rest)) :
    StateTransition.EvalsToInTime computer.step (initList computer input)
      (some (done true word rest)) (2 * input.length + 2) := by
  simpa [result, h] using run input

/-- Every malformed input produces a failure flag with all three stacks empty. -/
def malformedRun (input : List Bool) (h : Encoding.unframe input = none) :
    StateTransition.EvalsToInTime computer.step (initList computer input)
      (some (done false [] [])) (2 * input.length + 2) := by
  simpa [result, h] using run input

/-- Parsing a valid framed prefix takes exactly `3|word| + 2` transitions,
regardless of the length or contents of the remaining suffix. -/
def frameAppendRun (word rest : List Bool) :
    StateTransition.EvalsToInTime computer.step
      (initList computer (Encoding.frame word ++ rest))
      (some (done true word rest)) (3 * word.length + 2) where
  steps := 3 * word.length + 2
  evals_in_steps := by
    simpa [result, Encoding.unframe_frame_append, parseSteps_frame_append, cfg_init]
      using parse_evals (Encoding.frame word ++ rest) []
  steps_le_m := Nat.le_refl _

@[simp] theorem frameAppendRun_steps (word rest : List Bool) :
    (frameAppendRun word rest).steps = 3 * word.length + 2 := rfl

/-- The parser exposes the first codeword of any R1 product, without computing
the component decoder or touching the right component's bits. -/
def productRun {α β : Type} (ea : Encoding.BitEncoding α) (eb : Encoding.BitEncoding β)
    (a : α) (b : β) :
    StateTransition.EvalsToInTime computer.step
      (initList computer ((Encoding.prod ea eb).encode (a, b)))
      (some (done true (ea.encode a) (eb.encode b)))
      (3 * (ea.encode a).length + 2) :=
  frameAppendRun (ea.encode a) (eb.encode b)

/-- The first request parser step is a concrete instance of the same machine. -/
def requestOuterRun (r : ProgramEncoding.Request) :
    StateTransition.EvalsToInTime computer.step
      (initList computer (ProgramEncoding.request.encode r))
      (some (done true (Encoding.input.encode r.problem)
        ((Encoding.prod Encoding.output (Encoding.prod Encoding.output Encoding.bits)).encode
          (r.epsilon, (r.delta, r.tape)))))
      (3 * (Encoding.input.encode r.problem).length + 2) :=
  productRun Encoding.input
    (Encoding.prod Encoding.output (Encoding.prod Encoding.output Encoding.bits))
    r.problem (r.epsilon, (r.delta, r.tape))

end Unframing

end Counting.Algorithm.KarpLubyMachine
