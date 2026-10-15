import Counting.Computation.PolyTime

set_option backward.isDefEq.respectTransparency false

/-!
# Finite alphabet conversion by an actual mapped reversal

This generalizes the two-stack execution pattern in F1's
`Counting.Examples.mapReverseComputer` to distinct finite input/output alphabets.
A symbol lookup is a finite table. The run proves the entire strict halt-list
configuration and exactly one transition per input symbol plus one halt step.
-/
namespace Counting.WitnessMachines.MappedReverse

open Turing Computability Turing.TM2.Stmt Counting.Computation

inductive Stack | input | output deriving DecidableEq, Fintype

def Alphabet (I O : Type) : Stack → Type
  | .input => I
  | .output => O

variable {I O : Type} [Fintype I] [Fintype O] [Inhabited I]

abbrev machine (φ : I → O) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet I O
  Λ := Unit
  main := ()
  σ := Option I
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype I)
  m _ := pop .input (fun _ x => x)
    (branch Option.isSome
      (push .output (fun x => φ (x.getD default))
        (load (fun _ => none) (goto (fun _ => ()))))
      (load (fun _ => none) halt))

instance alphabetFintype (φ : I → O) (k : (machine φ).K) : Fintype ((machine φ).Γ k) := by
  cases k <;> dsimp [machine, Alphabet] <;> infer_instance

def cfg (φ : I → O) (input : List I) (output : List O) : (machine φ).Cfg where
  l := some ()
  var := none
  stk | .input => input | .output => output

@[simp] theorem cfg_init (φ : I → O) (word : List I) :
    cfg φ word [] = initList (machine φ) word := by
  unfold cfg initList
  congr 1
  funext k
  cases k <;> rfl

@[simp] theorem step_cons (φ : I → O) (a : I) (word : List I) (output : List O) :
    (machine φ).step (cfg φ (a :: word) output) =
      some (cfg φ word (φ a :: output)) := by
  simp [FinTM2.step, TM2.step, machine, cfg, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp

@[simp] theorem step_nil (φ : I → O) (output : List O) :
    (machine φ).step (cfg φ [] output) = some (haltList (machine φ) output) := by
  simp [FinTM2.step, TM2.step, machine, cfg, haltList, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp

def run (φ : I → O) (word : List I) (output : List O) :
    StateTransition.EvalsToInTime (machine φ).step (cfg φ word output)
      (some (haltList (machine φ) ((word.map φ).reverse ++ output))) (word.length + 1) where
  steps := word.length + 1
  evals_in_steps := by
    induction word generalizing output with
    | nil => exact step_nil φ output
    | cons a word ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip bind (machine φ).step)^[word.length + 1]
        ((machine φ).step (cfg φ (a :: word) output)) = _
      rw [step_cons]
      simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
        using ih (φ a :: output)
  steps_le_m := Nat.le_refl _

@[simp] theorem run_steps (φ : I → O) (word : List I) (output : List O) :
    (run φ word output).steps = word.length + 1 := rfl

def outputs (φ : I → O) (word : List I) :
    TM2OutputsInTime (machine φ) word (some (word.map φ).reverse) (word.length + 1) := by
  simpa only [TM2OutputsInTime, Option.map_some, cfg_init, List.append_nil] using run φ word []

noncomputable def polyTime (φ : I → O) :
    PolyTime (encodingList I) (encodingList O) (fun word => (word.map φ).reverse) where
  tm := machine φ
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun word := by
    change TM2OutputsInTime (machine φ) (List.map id word)
      (some (List.map id (word.map φ).reverse)) ((Polynomial.X + 1).eval word.length)
    simpa using outputs φ word
  finiteAlphabets := alphabetFintype φ

end Counting.WitnessMachines.MappedReverse
