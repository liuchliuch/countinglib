import Counting.WitnessMachines.MappedReverse
import PlanarHom.Complexity

set_option backward.isDefEq.respectTransparency false

/-!
# Tagged pairs to framed binary pairs

Three finite stacks scan the left and right tagged streams, construct the reverse
of the framed word, and restore the output order. The boundary transition puts
back the first right-tagged symbol, so the empty witness uses the same contract.
The proof architecture follows the accepted F1/R1 explicit-configuration runs;
the codec is the original PH `BitEncoding.prod`, not a new definition of pairing.
-/
namespace Counting.WitnessMachines.TaggedToFramed
open Turing Computability Turing.TM2.Stmt Counting.Computation
open PlanarHom.Complexity

abbrev Tag := Bool ⊕ Bool
inductive Stack | input | scratch | output deriving DecidableEq, Fintype
inductive Phase | first | second | restore deriving DecidableEq, Fintype

def Alphabet : Stack → Type
  | .input => Tag
  | .scratch | .output => Bool

abbrev Register := Option Tag × Option Bool

def bit (a : Tag) : Bool := a.elim id id

def reset (p : Phase) : TM2.Stmt Alphabet Phase Register :=
  load (fun _ => (none, none)) (goto (fun _ => p))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Phase
  main := .first
  σ := Register
  initialState := (none, none)
  Γk₀Fin := inferInstanceAs (Fintype Tag)
  m
    | .first => pop .input (fun _ a => (a, none))
        (branch (fun v => v.1.isSome)
          (branch (fun v => (v.1.getD (.inl false)).isLeft)
            (push .scratch (fun _ => true)
              (push .scratch (fun v => bit (v.1.getD (.inl false))) (reset .first)))
            (push .input (fun v => v.1.getD (.inl false))
              (push .scratch (fun _ => false) (reset .second))))
          (push .scratch (fun _ => false) (reset .second)))
    | .second => pop .input (fun _ a => (a, none))
        (branch (fun v => v.1.isSome)
          (push .scratch (fun v => bit (v.1.getD (.inr false))) (reset .second))
          (reset .restore))
    | .restore => pop .scratch (fun _ b => (none, b))
        (branch (fun v => v.2.isSome)
          (push .output (fun v => v.2.getD false) (reset .restore))
          (load (fun _ => (none, none)) halt))

instance alphabetFintype (k : machine.K) : Fintype (machine.Γ k) := by
  cases k <;> dsimp [machine, Alphabet] <;> infer_instance

def cfg (phase : Phase) (input : List Tag) (scratch output : Bits) : machine.Cfg where
  l := some phase
  var := (none, none)
  stk | .input => input | .scratch => scratch | .output => output

@[simp] theorem cfg_init (word : List Tag) :
    cfg .first word [] [] = initList machine word := by
  unfold cfg initList
  congr 1
  funext k
  cases k <;> rfl

@[simp] theorem first_cons (b : Bool) (word : List Tag) (scratch output : Bits) :
    machine.step (cfg .first (.inl b :: word) scratch output) =
      some (cfg .first word (b :: true :: scratch) output) := by
  simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, reset, bit]
  congr 2
  funext k
  cases k <;> simp

@[simp] theorem boundary (word scratch output : Bits) :
    machine.step (cfg .first (word.map Sum.inr) scratch output) =
      some (cfg .second (word.map Sum.inr) (false :: scratch) output) := by
  cases word <;> simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, reset, bit]
  all_goals congr 2; funext k; cases k <;> simp

@[simp] theorem second_cons (b : Bool) (word scratch output : Bits) :
    machine.step (cfg .second ((b :: word).map Sum.inr) scratch output) =
      some (cfg .second (word.map Sum.inr) (b :: scratch) output) := by
  simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, reset, bit]
  congr 2
  funext k
  cases k <;> simp

@[simp] theorem second_nil (scratch output : Bits) :
    machine.step (cfg .second [] scratch output) = some (cfg .restore [] scratch output) := by
  simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, reset]

@[simp] theorem restore_cons (b : Bool) (scratch output : Bits) :
    machine.step (cfg .restore [] (b :: scratch) output) =
      some (cfg .restore [] scratch (b :: output)) := by
  simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, reset]
  congr 2
  funext k
  cases k <;> simp

@[simp] theorem restore_nil (output : Bits) :
    machine.step (cfg .restore [] [] output) = some (haltList machine output) := by
  simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, haltList]
  congr 2
  funext k
  cases k <;> simp

def payload (word : Bits) : Bits := word.flatMap (fun b => [true, b])

@[simp] theorem payload_length (word : Bits) : (payload word).length = 2 * word.length := by
  induction word with
  | nil => rfl
  | cons b word ih => simp [payload] at ih ⊢; omega

theorem frame_eq_payload (word : Bits) : BitEncoding.frame word = payload word ++ [false] := by
  induction word with
  | nil => rfl
  | cons b word ih => simp [BitEncoding.frame, payload, ih]

def firstRun (left right scratch output : Bits) :
    StateTransition.EvalsToInTime machine.step
      (cfg .first (left.map Sum.inl ++ right.map Sum.inr) scratch output)
      (some (cfg .second (right.map Sum.inr) (false :: (payload left).reverse ++ scratch) output))
      (left.length + 1) where
  steps := left.length + 1
  evals_in_steps := by
    induction left generalizing scratch with
    | nil => exact boundary right scratch output
    | cons b left ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip bind machine.step)^[left.length + 1]
        (machine.step (cfg .first (.inl b :: (left.map Sum.inl ++ right.map Sum.inr)) scratch output)) = _
      rw [first_cons]
      simpa only [payload, List.flatMap_cons, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.append_assoc, List.cons_append, List.nil_append] using ih (b :: true :: scratch)
  steps_le_m := Nat.le_refl _

def secondRun (right scratch output : Bits) :
    StateTransition.EvalsToInTime machine.step
      (cfg .second (right.map Sum.inr) scratch output)
      (some (cfg .restore [] (right.reverse ++ scratch) output)) (right.length + 1) where
  steps := right.length + 1
  evals_in_steps := by
    induction right generalizing scratch with
    | nil => exact second_nil scratch output
    | cons b right ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip bind machine.step)^[right.length + 1]
        (machine.step (cfg .second ((b :: right).map Sum.inr) scratch output)) = _
      rw [second_cons]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (b :: scratch)
  steps_le_m := Nat.le_refl _

def restoreRun (scratch output : Bits) :
    StateTransition.EvalsToInTime machine.step (cfg .restore [] scratch output)
      (some (haltList machine (scratch.reverse ++ output))) (scratch.length + 1) where
  steps := scratch.length + 1
  evals_in_steps := by
    induction scratch generalizing output with
    | nil => exact restore_nil output
    | cons b scratch ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip bind machine.step)^[scratch.length + 1]
        (machine.step (cfg .restore [] (b :: scratch) output)) = _
      rw [restore_cons]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (b :: output)
  steps_le_m := Nat.le_refl _

/-- Complete strict output, including empty input/scratch stacks and reset state. -/
def outputs (left right : Bits) :
    TM2OutputsInTime machine (left.map Sum.inl ++ right.map Sum.inr)
      (some (BitEncoding.frame left ++ right)) (3 * left.length + 2 * right.length + 4) := by
  have first := firstRun left right [] []
  simp only [List.append_nil] at first
  have second := secondRun right (false :: (payload left).reverse) []
  have third := restoreRun (right.reverse ++ false :: (payload left).reverse) []
  have firstTwo :=  StateTransition.EvalsToInTime.trans machine.step _ _ _ _ _ first second
  have full := StateTransition.EvalsToInTime.trans machine.step _ _ _ _ _ firstTwo third
  have output_eq : (right.reverse ++ false :: (payload left).reverse).reverse ++ [] =
      BitEncoding.frame left ++ right := by
    simp [frame_eq_payload, List.reverse_append, List.reverse_cons, List.append_assoc]
  rw [output_eq] at full
  have time_eq : ((right.reverse ++ false :: (payload left).reverse).length + 1) +
      (right.length + 1 + (left.length + 1)) =
      3 * left.length + 2 * right.length + 4 := by simp; omega
  rw [time_eq] at full
  simpa only [TM2OutputsInTime, Option.map_some, cfg_init] using full

abbrev taggedPair : Encoding (Bits × Bits) Tag :=
  encodingProd BitEncoding.bits.toFinEncoding (encodingList Bool)

abbrev framedPair : Encoding (Bits × Bits) Bool :=
  (BitEncoding.bits.prod BitEncoding.bits).toFinEncoding

/-- A real linear-time identity between the two pair representations. -/
noncomputable def polyTime : PolyTime taggedPair framedPair id where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 4
  outputsFun pair := by
    have h := outputs pair.1 pair.2
    refine { steps := h.steps, evals_in_steps := ?_, steps_le_m := ?_ }
    · simp only [Equiv.refl, List.map_id]
      exact h.evals_in_steps
    · apply h.steps_le_m.trans
      simp [taggedPair, encodingProd, encodingList, BitEncoding.toFinEncoding, BitEncoding.bits]
      omega
  finiteAlphabets := alphabetFintype

end Counting.WitnessMachines.TaggedToFramed
