import Counting.Computation.PolyTime
import Counting.Algorithm.KarpLuby.ProgramEncoding

/-!
# A finite TM2 implementation of the request codec's framing operation

The public codec is exactly `KarpLuby.Encoding.frame`. Three Boolean stacks,
two instruction labels, and an `Option Bool` register suffice. A reverse pass
is followed by an escaping pass; both passes consume one symbol per TM2
transition. The final configuration has empty input and scratch stacks and a
reset register. The execution also works with an arbitrary suffix already on
the output stack, exposing the operation needed by `Encoding.prod`.

The proof architecture (explicit configurations, single-step equations,
inductive timed runs, and an F1 witness) is adapted from F1's
`Counting/Examples/Machines.lean`, `mapReverseComputer` and `mapReverseRun`.
The codec itself is imported from the unique R1 provider. The old Hidden
Circuits `Complexity/PairSerialization.lean` was consulted for its suffix
preservation contract; neither its oracle program language nor its dependency
closure is imported or copied. No natural or rational operation is placed in
finite control.
-/

namespace Counting.Algorithm.KarpLubyMachine

open Turing Computability
open Turing.TM2.Stmt
open Counting.Computation

namespace Framing

open KarpLuby

/-- Escaped payload without the terminating `false`; a proof-side invariant. -/
def payload (word : List Bool) : List Bool := word.flatMap (fun b => [true, b])

@[simp] theorem payload_nil : payload [] = [] := rfl

@[simp] theorem payload_cons (b : Bool) (word : List Bool) :
    payload (b :: word) = true :: b :: payload word := rfl

@[simp] theorem payload_append (left right : List Bool) :
    payload (left ++ right) = payload left ++ payload right := by
  simp [payload]

theorem frame_eq_payload (word : List Bool) :
    Encoding.frame word = payload word ++ [false] := by
  induction word with
  | nil => rfl
  | cons b word ih => simp [Encoding.frame, ih]

/-- `none` is input, `some false` scratch, and `some true` output.
The two phases only inspect a single optional Boolean. -/
abbrev computer : FinTM2 where
  K := Option Bool
  k₀ := none
  k₁ := some true
  Γ _ := Bool
  Λ := Bool
  main := false
  σ := Option Bool
  initialState := none
  m phase := if phase then
    pop (some false) (fun _ x => x)
      (branch Option.isSome
        (push (some true) (fun x => x.getD false)
          (push (some true) (fun _ => true)
            (load (fun _ => none) (goto (fun _ => true)))))
        (load (fun _ => none) halt))
    else
    pop none (fun _ x => x)
      (branch Option.isSome
        (push (some false) (fun x => x.getD false)
          (load (fun _ => none) (goto (fun _ => false))))
        (push (some true) (fun _ => false)
          (load (fun _ => none) (goto (fun _ => true)))))

/-- Every stack, including scratch, has the finite binary alphabet. -/
instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) :=
  inferInstanceAs (Fintype Bool)

/-- The configuration invariant records all three stack contents. -/
def cfg (phase : Bool) (input scratch output : List Bool) : computer.Cfg where
  l := some phase
  var := none
  stk k := match k with
    | none => input
    | some false => scratch
    | some true => output

@[simp] theorem cfg_init (word : List Bool) :
    cfg false word [] [] = initList computer word := by
  unfold cfg initList
  congr 1
  funext k
  rcases k with _ | (_ | _) <;> rfl

@[simp] theorem step_reverse_cons (b : Bool) (word scratch output : List Bool) :
    computer.step (cfg false (b :: word) scratch output) =
      some (cfg false word (b :: scratch) output) := by
  simp [FinTM2.step, TM2.step, computer, cfg, TM2.stepAux]
  congr 2
  funext k
  rcases k with _ | (_ | _) <;> simp

@[simp] theorem step_reverse_nil (scratch output : List Bool) :
    computer.step (cfg false [] scratch output) =
      some (cfg true [] scratch (false :: output)) := by
  simp [FinTM2.step, TM2.step, computer, cfg, TM2.stepAux]
  congr 2
  funext k
  rcases k with _ | (_ | _) <;> simp

@[simp] theorem step_emit_cons (b : Bool) (scratch output : List Bool) :
    computer.step (cfg true [] (b :: scratch) output) =
      some (cfg true [] scratch (true :: b :: output)) := by
  simp [FinTM2.step, TM2.step, computer, cfg, TM2.stepAux]
  congr 2
  funext k
  rcases k with _ | (_ | _) <;> simp

@[simp] theorem step_emit_nil (output : List Bool) :
    computer.step (cfg true [] [] output) = some (haltList computer output) := by
  simp [FinTM2.step, TM2.step, computer, cfg, haltList, TM2.stepAux]
  congr 2
  funext k
  rcases k with _ | (_ | _) <;> simp

/-- The first pass consumes the input, including the phase-switch transition. -/
def reverseRun (word scratch output : List Bool) :
    StateTransition.EvalsToInTime computer.step
      (cfg false word scratch output)
      (some (cfg true [] (word.reverse ++ scratch) (false :: output)))
      (word.length + 1) where
  steps := word.length + 1
  evals_in_steps := by
    induction word generalizing scratch with
    | nil => exact step_reverse_nil scratch output
    | cons b word ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip bind computer.step)^[word.length + 1]
        (computer.step (cfg false (b :: word) scratch output)) = _
      rw [step_reverse_cons]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append]
        using ih (b :: scratch)
  steps_le_m := Nat.le_refl _

@[simp] theorem reverseRun_steps (word scratch output : List Bool) :
    (reverseRun word scratch output).steps = word.length + 1 := rfl

/-- The second pass escapes one scratch symbol per transition and then halts. -/
def emitRun (scratch output : List Bool) :
    StateTransition.EvalsToInTime computer.step
      (cfg true [] scratch output)
      (some (haltList computer (payload scratch.reverse ++ output)))
      (scratch.length + 1) where
  steps := scratch.length + 1
  evals_in_steps := by
    induction scratch generalizing output with
    | nil => exact step_emit_nil output
    | cons b scratch ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip bind computer.step)^[scratch.length + 1]
        (computer.step (cfg true [] (b :: scratch) output)) = _
      rw [step_emit_cons]
      simpa only [List.reverse_cons, payload_append, payload_cons, payload_nil,
        List.append_assoc, List.cons_append, List.nil_append]
        using ih (true :: b :: output)
  steps_le_m := Nat.le_refl _

@[simp] theorem emitRun_steps (scratch output : List Bool) :
    (emitRun scratch output).steps = scratch.length + 1 := rfl

/-- Framing prepends the escaped input to an arbitrary existing output suffix.
This is the complete clean configuration contract, not an output projection. -/
def appendRun (word suffix : List Bool) :
    StateTransition.EvalsToInTime computer.step
      (cfg false word [] suffix)
      (some (haltList computer (Encoding.frame word ++ suffix)))
      (2 * word.length + 2) where
  steps := 2 * word.length + 2
  evals_in_steps := by
    have first := (reverseRun word [] suffix).evals_in_steps
    have second := (emitRun word.reverse (false :: suffix)).evals_in_steps
    change (flip bind computer.step)^[word.length + 1]
      (some (cfg false word [] suffix)) =
      some (cfg true [] (word.reverse ++ []) (false :: suffix)) at first
    change (flip bind computer.step)^[word.reverse.length + 1]
      (some (cfg true [] word.reverse (false :: suffix))) =
      some (haltList computer (payload word.reverse.reverse ++ (false :: suffix))) at second
    rw [show 2 * word.length + 2 = (word.length + 1) + (word.length + 1) by omega,
      Function.iterate_add_apply, first, List.append_nil]
    simpa only [List.length_reverse, List.reverse_reverse, frame_eq_payload,
      List.append_assoc, List.singleton_append] using second
  steps_le_m := Nat.le_refl _

@[simp] theorem appendRun_steps (word suffix : List Bool) :
    (appendRun word suffix).steps = 2 * word.length + 2 := rfl

/-- The public raw-bit codec is materialized in at most `2n + 2` transitions. -/
def outputs (word : List Bool) :
    TM2OutputsInTime computer word (some (Encoding.frame word))
      (2 * word.length + 2) where
  steps := 2 * word.length + 2
  evals_in_steps := by
    simpa only [Option.map_some, cfg_init, List.append_nil, appendRun_steps]
      using (appendRun word []).evals_in_steps
  steps_le_m := Nat.le_refl _

@[simp] theorem outputs_steps (word : List Bool) :
    (outputs word).steps = 2 * word.length + 2 := rfl

/-- A concrete F1 finite-machine witness for the unchanged R1 framing codec. -/
noncomputable def polyTime :
    PolyTime Encoding.bits Encoding.bits Encoding.frame where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun word := by
    change TM2OutputsInTime computer (List.map id word)
      (some (List.map id (Encoding.frame word)))
      ((2 * Polynomial.X + 2).eval word.length)
    simpa using outputs word
  finiteAlphabets := alphabetFintype

theorem inFP : InFP Encoding.bits Encoding.bits Encoding.frame := ⟨polyTime⟩

/-- The same transducer frames an already serialized field under any faithful
binary encoding. The field's encoder is the input representation, not a free
operation performed by the machine. -/
noncomputable def encodePolyTime {α : Type} (e : Encoding.BitEncoding α) :
    PolyTime e Encoding.bits (fun a => Encoding.frame (e.encode a)) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun a := by
    change TM2OutputsInTime computer (List.map id (e.encode a))
      (some (List.map id (Encoding.frame (e.encode a))))
      ((2 * Polynomial.X + 2).eval (e.encode a).length)
    simpa using outputs (e.encode a)
  finiteAlphabets := alphabetFintype

/-- The suffix-preserving machine implements the exact product-encoding step. -/
def productRun {α β : Type} (ea : Encoding.BitEncoding α) (eb : Encoding.BitEncoding β)
    (a : α) (b : β) :
    StateTransition.EvalsToInTime computer.step
      (cfg false (ea.encode a) [] (eb.encode b))
      (some (haltList computer ((Encoding.prod ea eb).encode (a, b))))
      (2 * (ea.encode a).length + 2) :=
  appendRun (ea.encode a) (eb.encode b)

/-- The outer request-framing operation is an actual instance of the same
machine. Constructing the inner serialized suffix is a separate obligation. -/
def requestOuterRun (r : ProgramEncoding.Request) :
    StateTransition.EvalsToInTime computer.step
      (cfg false (Encoding.input.encode r.problem) []
        ((Encoding.prod Encoding.output (Encoding.prod Encoding.output Encoding.bits)).encode
          (r.epsilon, (r.delta, r.tape))))
      (some (haltList computer (ProgramEncoding.request.encode r)))
      (2 * (Encoding.input.encode r.problem).length + 2) :=
  productRun Encoding.input
    (Encoding.prod Encoding.output (Encoding.prod Encoding.output Encoding.bits))
    r.problem (r.epsilon, (r.delta, r.tape))

end Framing

end Counting.Algorithm.KarpLubyMachine
