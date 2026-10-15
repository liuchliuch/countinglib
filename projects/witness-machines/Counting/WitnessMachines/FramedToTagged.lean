import Counting.WitnessMachines.TaggedToFramed

set_option backward.isDefEq.respectTransparency false

/-! The inverse representation transducer parses the framed instance, tags each
instance/witness bit, and reverses its scratch stack into strict clean output. -/
namespace Counting.WitnessMachines.FramedToTagged
open Turing Computability Turing.TM2.Stmt Counting.Computation
open PlanarHom.Complexity

abbrev Tag := Bool ⊕ Bool
inductive Stack | input | scratch | output deriving DecidableEq, Fintype
inductive Phase | first | second | restore deriving DecidableEq, Fintype

def Alphabet : Stack → Type
  | .input => Bool
  | .scratch | .output => Tag

abbrev Register := Option Bool × Option Tag

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
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m
    | .first => pop .input (fun _ a => (a, none))
        (branch (fun v => v.1.getD false)
          (pop .input (fun _ b => (b, none))
            (push .scratch (fun v => .inl (v.1.getD false)) (reset .first)))
          (reset .second))
    | .second => pop .input (fun _ a => (a, none))
        (branch (fun v => v.1.isSome)
          (push .scratch (fun v => .inr (v.1.getD false)) (reset .second))
          (reset .restore))
    | .restore => pop .scratch (fun _ b => (none, b))
        (branch (fun v => v.2.isSome)
          (push .output (fun v => v.2.getD (.inl false)) (reset .restore))
          (load (fun _ => (none, none)) halt))

instance alphabetFintype (k : machine.K) : Fintype (machine.Γ k) := by
  cases k <;> dsimp [machine, Alphabet] <;> infer_instance

def cfg (phase : Phase) (input : Bits) (scratch output : List Tag) : machine.Cfg where
  l := some phase
  var := (none, none)
  stk | .input => input | .scratch => scratch | .output => output

@[simp] theorem cfg_init (word : Bits) :
    cfg .first word [] [] = initList machine word := by
  unfold cfg initList
  congr 1
  funext k
  cases k <;> rfl

@[simp] theorem first_cons (b : Bool) (word : Bits) (scratch output : List Tag) :
    machine.step (cfg .first (true :: b :: word) scratch output) =
      some (cfg .first word (.inl b :: scratch) output) := by
  simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, reset]
  congr 2
  funext k
  cases k <;> simp

@[simp] theorem boundary (word : Bits) (scratch output : List Tag) :
    machine.step (cfg .first (false :: word) scratch output) =
      some (cfg .second word scratch output) := by
  simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, reset]
  congr 2
  funext k
  cases k <;> simp

@[simp] theorem second_cons (b : Bool) (word : Bits) (scratch output : List Tag) :
    machine.step (cfg .second (b :: word) scratch output) =
      some (cfg .second word (.inr b :: scratch) output) := by
  simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, reset]
  congr 2
  funext k
  cases k <;> simp

@[simp] theorem second_nil (scratch output : List Tag) :
    machine.step (cfg .second [] scratch output) = some (cfg .restore [] scratch output) := by
  simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, reset]

@[simp] theorem restore_cons (b : Tag) (scratch output : List Tag) :
    machine.step (cfg .restore [] (b :: scratch) output) =
      some (cfg .restore [] scratch (b :: output)) := by
  simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, reset]
  congr 2
  funext k
  cases k <;> simp

@[simp] theorem restore_nil (output : List Tag) :
    machine.step (cfg .restore [] [] output) = some (haltList machine output) := by
  simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux, haltList]
  congr 2
  funext k
  cases k <;> simp

def firstRun (left right : Bits) (scratch output : List Tag) :
    StateTransition.EvalsToInTime machine.step
      (cfg .first (BitEncoding.frame left ++ right) scratch output)
      (some (cfg .second right ((left.map Sum.inl).reverse ++ scratch) output))
      (left.length + 1) where
  steps := left.length + 1
  evals_in_steps := by
    induction left generalizing scratch with
    | nil => exact boundary right scratch output
    | cons b left ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip bind machine.step)^[left.length + 1]
        (machine.step (cfg .first (true :: b :: (BitEncoding.frame left ++ right)) scratch output)) = _
      rw [first_cons]
      simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
        using ih (.inl b :: scratch)
  steps_le_m := Nat.le_refl _

def secondRun (right : Bits) (scratch output : List Tag) :
    StateTransition.EvalsToInTime machine.step (cfg .second right scratch output)
      (some (cfg .restore [] ((right.map Sum.inr).reverse ++ scratch) output)) (right.length + 1) where
  steps := right.length + 1
  evals_in_steps := by
    induction right generalizing scratch with
    | nil => exact second_nil scratch output
    | cons b right ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip bind machine.step)^[right.length + 1]
        (machine.step (cfg .second (b :: right) scratch output)) = _
      rw [second_cons]
      simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
        using ih (.inr b :: scratch)
  steps_le_m := Nat.le_refl _

def restoreRun (scratch output : List Tag) :
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

def outputs (left right : Bits) :
    TM2OutputsInTime machine (BitEncoding.frame left ++ right)
      (some (left.map Sum.inl ++ right.map Sum.inr)) (2 * left.length + 2 * right.length + 3) := by
  have first := firstRun left right [] []
  simp only [List.append_nil] at first
  have second := secondRun right (left.map Sum.inl).reverse []
  have third := restoreRun ((right.map Sum.inr).reverse ++ (left.map Sum.inl).reverse) []
  have firstTwo :=  StateTransition.EvalsToInTime.trans machine.step _ _ _ _ _ first second
  have full := StateTransition.EvalsToInTime.trans machine.step _ _ _ _ _ firstTwo third
  have output_eq : ((right.map Sum.inr).reverse ++ (left.map Sum.inl).reverse).reverse ++ [] =
      left.map Sum.inl ++ right.map Sum.inr := by simp
  rw [output_eq] at full
  have time_eq : (((right.map Sum.inr).reverse ++ (left.map Sum.inl).reverse).length + 1) +
      (right.length + 1 + (left.length + 1)) =
      2 * left.length + 2 * right.length + 3 := by simp; omega
  rw [time_eq] at full
  simpa only [TM2OutputsInTime, Option.map_some, cfg_init] using full

noncomputable def polyTime :
    PolyTime TaggedToFramed.framedPair TaggedToFramed.taggedPair id where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 1
  outputsFun pair := by
    have h := outputs pair.1 pair.2
    refine { steps := h.steps, evals_in_steps := ?_, steps_le_m := ?_ }
    · simp only [Equiv.refl, List.map_id]
      exact h.evals_in_steps
    · apply h.steps_le_m.trans
      simp [TaggedToFramed.framedPair, BitEncoding.toFinEncoding, BitEncoding.prod,
        BitEncoding.bits, BitEncoding.frame_length]
      omega
  finiteAlphabets := alphabetFintype

end Counting.WitnessMachines.FramedToTagged
