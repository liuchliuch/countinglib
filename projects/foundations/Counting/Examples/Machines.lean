import Counting.Computation.PolyTime
import Counting.Encoding.Basic
import Counting.Complexity.Reduction

/-!
# Concrete linear-time clients

Two Boolean stacks and three control states implement a mapped reversal.
Specializing the finite Boolean lookup table to identity computes reversal;
specializing it to the constant `true` computes the length in unary.
Both proofs inspect actual TM2 transitions and require a clean halting
configuration, including an empty input stack and reset control state.
-/

namespace Counting.Examples

open Turing Computability
open Turing.TM2.Stmt
open Counting.Computation

/-- A finite two-stack transducer. The parameter is a lookup table on the
finite Boolean alphabet, so it cannot hide an unbounded computation. -/
abbrev mapReverseComputer (φ : Bool → Bool) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m _ := pop false (fun _ x => x)
    (branch Option.isSome
      (push true (fun x => φ (x.getD false))
        (load (fun _ => none) (goto (fun _ => ()))))
      (load (fun _ => none) halt))

/-- The invariant separates the unprocessed suffix from the reversed output. -/
def mapReverseCfg (φ : Bool → Bool) (input output : List Bool) :
    (mapReverseComputer φ).Cfg where
  l := some ()
  var := none
  stk k := if k then output else input

@[simp] theorem mapReverseCfg_init (φ : Bool → Bool) (l : List Bool) :
    mapReverseCfg φ l [] = initList (mapReverseComputer φ) l := by
  unfold mapReverseCfg initList
  congr 1
  funext k
  cases k <;> rfl

@[simp] theorem mapReverseComputer_step_cons (φ : Bool → Bool)
    (b : Bool) (l acc : List Bool) :
    (mapReverseComputer φ).step (mapReverseCfg φ (b :: l) acc) =
      some (mapReverseCfg φ l (φ b :: acc)) := by
  simp [FinTM2.step, TM2.step, mapReverseComputer, mapReverseCfg, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp

@[simp] theorem mapReverseComputer_step_nil (φ : Bool → Bool) (acc : List Bool) :
    (mapReverseComputer φ).step (mapReverseCfg φ [] acc) =
      some (haltList (mapReverseComputer φ) acc) := by
  simp [FinTM2.step, TM2.step, mapReverseComputer, mapReverseCfg, haltList, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp

/-- The execution consumes one input bit per transition, followed by a halting
transition. The entire configuration, not only its output projection, is proved. -/
def mapReverseRun (φ : Bool → Bool) (l acc : List Bool) :
    StateTransition.EvalsToInTime (mapReverseComputer φ).step
      (mapReverseCfg φ l acc)
      (some (haltList (mapReverseComputer φ) ((l.map φ).reverse ++ acc)))
      (l.length + 1) := by
  induction l generalizing acc with
  | nil =>
      exact { steps := 1
              evals_in_steps := mapReverseComputer_step_nil φ acc
              steps_le_m := Nat.le_refl 1 }
  | cons b l ih =>
      simpa only [List.length_cons, List.map_cons, List.reverse_cons,
        List.append_assoc, List.singleton_append] using
        StateTransition.EvalsToInTime.trans (mapReverseComputer φ).step
          1 (l.length + 1)
          (mapReverseCfg φ (b :: l) acc)
          (mapReverseCfg φ l (φ b :: acc))
          (some (haltList (mapReverseComputer φ) ((l.map φ).reverse ++ (φ b :: acc))))
          { steps := 1
            evals_in_steps := mapReverseComputer_step_cons φ b l acc
            steps_le_m := Nat.le_refl 1 }
          (ih (φ b :: acc))

/-- A mapped reversal on raw bit strings costs at most `n + 1` transitions. -/
def mapReverseComputer_outputs (φ : Bool → Bool) (l : List Bool) :
    TM2OutputsInTime (mapReverseComputer φ) l (some (l.map φ).reverse)
      (l.length + 1) := by
  simpa only [TM2OutputsInTime, Option.map_some, mapReverseCfg_init, List.append_nil]
    using mapReverseRun φ l []

/-- A nonconstant transformation of arbitrarily long bit strings, with its
concrete finite-machine implementation and linear polynomial. -/
noncomputable def reversePolyTime :
    PolyTime (encodingList Bool) (encodingList Bool) List.reverse where
  tm := mapReverseComputer id
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun l := by
    change TM2OutputsInTime (mapReverseComputer id) (List.map id l)
      (some (List.map id l.reverse)) ((Polynomial.X + 1).eval l.length)
    simpa only [List.map_id, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      using mapReverseComputer_outputs id l
  finiteAlphabets _ := inferInstanceAs (Fintype Bool)

/-- Reversal is in FP under the ordinary uncompressed bit-string encoding. -/
theorem reverse_inFP : InFP (encodingList Bool) (encodingList Bool) List.reverse :=
  ⟨reversePolyTime⟩

private theorem map_true_reverse (l : List Bool) :
    (l.map (fun _ => true)).reverse = unaryEncodeNat l.length := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      simp only [List.map_cons, List.reverse_cons, List.length_cons, unaryEncodeNat]
      rw [ih]
      have aux (n : ℕ) : unaryEncodeNat n ++ [true] = true :: unaryEncodeNat n := by
        induction n with
        | zero => rfl
        | succ n hn => simpa only [unaryEncodeNat, List.cons_append] using congrArg (List.cons true) hn
      exact aux l.length

/-- Materializing the unary length output takes linear time on a real machine.
The output is not a free natural-number register. -/
noncomputable def lengthPolyTime :
    PolyTime (encodingList Bool) Counting.Encoding.unaryNat List.length where
  tm := mapReverseComputer (fun _ => true)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun l := by
    change TM2OutputsInTime (mapReverseComputer (fun _ => true)) (List.map id l)
      (some (List.map id (unaryEncodeNat l.length))) ((Polynomial.X + 1).eval l.length)
    simpa only [List.map_id, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one, map_true_reverse]
      using mapReverseComputer_outputs (fun _ => true) l
  finiteAlphabets _ := inferInstanceAs (Fintype Bool)

/-- A nonconstant natural-valued FP problem, with an explicit output encoding. -/
theorem length_inFP :
    InFP (encodingList Bool) Counting.Encoding.unaryNat List.length :=
  ⟨lengthPolyTime⟩

/-- The generic composition compiler is instantiated on two real transducers. -/
noncomputable def reverseTwicePolyTime :
    PolyTime (encodingList Bool) (encodingList Bool) (List.reverse ∘ List.reverse) :=
  PolyTime.comp reversePolyTime reversePolyTime

/-- The composed transducers implement identity semantically. -/
theorem reverseTwice_eq (l : List Bool) : (List.reverse ∘ List.reverse) l = l :=
  List.reverse_reverse l

/-- Reversal preserves a nonconstant natural-valued counting problem and is an
actual parsimonious reduction with a proved finite-machine implementation. -/
noncomputable def reverseLengthReduction :
    Counting.Complexity.ParsimoniousReduction (encodingList Bool) (encodingList Bool)
      List.length List.length where
  map := List.reverse
  machine := reversePolyTime
  correct l := by simp

/-- A client of the proved reduction-composition theorem. -/
noncomputable def reverseLengthReductionTwice :
    Counting.Complexity.ParsimoniousReduction (encodingList Bool) (encodingList Bool)
      List.length List.length :=
  reverseLengthReduction.trans reverseLengthReduction

/-- The composed reduction really applies reversal twice. -/
theorem reverseLengthReductionTwice_map (l : List Bool) :
    reverseLengthReductionTwice.map l = l := by
  exact List.reverse_reverse l

/-- FP transport compiles the instance transformation and the target evaluator;
the resulting evaluator still computes a nonconstant natural number. -/
noncomputable def lengthViaReductionPolyTime :
    PolyTime (encodingList Bool) Counting.Encoding.unaryNat List.length :=
  reverseLengthReduction.computer lengthPolyTime

/-- A direct client of tractability transport for counting reductions. -/
theorem lengthViaReduction_inFP :
    InFP (encodingList Bool) Counting.Encoding.unaryNat List.length :=
  reverseLengthReduction.inFP length_inFP

/-- Two inputs distinguish the natural-valued problem used in the client. -/
theorem length_problem_nonconstant :
    (List.length ([] : List Bool)) ≠ List.length [true] := by decide

end Counting.Examples
