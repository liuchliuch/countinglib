import Counting.Complexity.SharpP
import Counting.Foundation.Witness

/-!
# A nonconstant finite-machine witness verifier

A four-state, one-stack TM2 scans the full tagged input/witness encoding. It
accepts exactly when at least one witness bit is true. The actual transition
proof charges one step per encoded symbol and one final clean-halting step.
-/

namespace Counting.Examples

open Turing Computability
open Turing.TM2.Stmt

/-- Instance bits are ignored by the predicate, while true witness bits accept. -/
def taggedWitnessBit : Bool ⊕ Bool → Bool
  | .inl _ => false
  | .inr b => b

/-- One stack, one program label, four finite states, and four alphabet symbols.
The first state bit accumulates acceptance; the second detects the end of input. -/
abbrev witnessAnyComputer : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool ⊕ Bool
  Λ := Unit
  main := ()
  σ := Bool × Bool
  initialState := (false, false)
  m _ := pop () (fun s x => (s.1 || (x.map taggedWitnessBit).getD false, x.isSome))
    (branch Prod.snd
      (load (fun s => (s.1, false)) (goto (fun _ => ())))
      (push () (fun s => Sum.inr s.1) (load (fun _ => (false, false)) halt)))

/-- The live invariant records the unprocessed input and the acceptance flag. -/
def witnessAnyCfg (seen : Bool) (input : List (Bool ⊕ Bool)) : witnessAnyComputer.Cfg where
  l := some ()
  var := (seen, false)
  stk _ := input

@[simp] theorem witnessAnyCfg_init (input : List (Bool ⊕ Bool)) :
    witnessAnyCfg false input = initList witnessAnyComputer input := by
  congr 1

@[simp] theorem witnessAnyComputer_step_cons (seen : Bool) (a : Bool ⊕ Bool)
    (l : List (Bool ⊕ Bool)) :
    witnessAnyComputer.step (witnessAnyCfg seen (a :: l)) =
      some (witnessAnyCfg (seen || taggedWitnessBit a) l) := by
  simp only [FinTM2.step, TM2.step, witnessAnyComputer, witnessAnyCfg, TM2.stepAux]
  congr 2

@[simp] theorem witnessAnyComputer_step_nil (seen : Bool) :
    witnessAnyComputer.step (witnessAnyCfg seen []) =
      some (haltList witnessAnyComputer [Sum.inr seen]) := by
  simp only [FinTM2.step, TM2.step, witnessAnyComputer, witnessAnyCfg, haltList, TM2.stepAux]
  congr 2
  simp
  funext k
  cases k
  rfl

/-- A concrete run ending in the complete clean halting configuration. -/
def witnessAnyRun (l : List (Bool ⊕ Bool)) (seen : Bool) :
    StateTransition.EvalsToInTime witnessAnyComputer.step
      (witnessAnyCfg seen l)
      (some (haltList witnessAnyComputer [Sum.inr (seen || l.any taggedWitnessBit)]))
      (l.length + 1) := by
  induction l generalizing seen with
  | nil =>
      exact { steps := 1
              evals_in_steps := by
                change witnessAnyComputer.step (witnessAnyCfg seen []) = _
                simpa only [List.any_nil, Bool.or_false] using witnessAnyComputer_step_nil seen
              steps_le_m := Nat.le_refl 1 }
  | cons a l ih =>
      simpa only [List.length_cons, List.any_cons, Bool.or_assoc] using
        StateTransition.EvalsToInTime.trans witnessAnyComputer.step
          1 (l.length + 1)
          (witnessAnyCfg seen (a :: l))
          (witnessAnyCfg (seen || taggedWitnessBit a) l)
          (some (haltList witnessAnyComputer
            [Sum.inr ((seen || taggedWitnessBit a) || l.any taggedWitnessBit)]))
          { steps := 1
            evals_in_steps := witnessAnyComputer_step_cons seen a l
            steps_le_m := Nat.le_refl 1 }
          (ih (seen || taggedWitnessBit a))

/-- One transition per symbol followed by the final output transition. -/
def witnessAnyComputer_outputs (l : List (Bool ⊕ Bool)) :
    TM2OutputsInTime witnessAnyComputer l
      (some [Sum.inr (l.any taggedWitnessBit)]) (l.length + 1) := by
  change StateTransition.EvalsToInTime witnessAnyComputer.step
    (initList witnessAnyComputer l)
    (some (haltList witnessAnyComputer [Sum.inr (l.any taggedWitnessBit)])) _
  simpa only [witnessAnyCfg_init, Bool.false_or] using witnessAnyRun l false

/-- A witness is accepted precisely when it has a true bit. -/
def witnessAnyAccept (x : List Bool × List Bool) : Bool := x.2.any id

/-- The input/witness tags are respected by the actual scanning predicate. -/
theorem tagged_witness_any (x w : List Bool) :
    ((encodingProd (encodingList Bool) (encodingList Bool)).encode (x, w)).any
      taggedWitnessBit = w.any id := by
  have hx : x.any (fun _ => false) = false := by
    induction x with
    | nil => rfl
    | cons b x ih => simpa only [List.any_cons, Bool.false_or] using ih
  simp [encodingProd, encodingList, List.any_append, List.any_map, Function.comp_def,
    taggedWitnessBit, hx]
  rfl

/-- A genuine linear-time finite verifier of a nonconstant witness predicate. -/
noncomputable def witnessAnyPolyTime : Holant.Complexity.PolyTime
    (encodingProd (encodingList Bool) (encodingList Bool))
    (Holant.Complexity.taggedBoolEncoding Bool) witnessAnyAccept where
  tm := witnessAnyComputer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun x := by
    rcases x with ⟨x, w⟩
    change TM2OutputsInTime witnessAnyComputer
      (List.map id ((encodingProd (encodingList Bool) (encodingList Bool)).encode (x, w)))
      (some (List.map id [Sum.inr (w.any id)]))
      ((Polynomial.X + 1).eval
        ((encodingProd (encodingList Bool) (encodingList Bool)).encode (x, w)).length)
    simpa only [Equiv.refl_symm, Equiv.refl_apply, List.map_id,
      Holant.Complexity.taggedBoolEncoding, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one, tagged_witness_any, witnessAnyAccept]
      using witnessAnyComputer_outputs
        ((encodingProd (encodingList Bool) (encodingList Bool)).encode (x, w))
  finiteAlphabets _ := inferInstanceAs (Fintype (Bool ⊕ Bool))

/-- Empty or all-false witnesses reject, whereas a true witness bit accepts. -/
theorem witnessAnyAccept_nonconstant :
    witnessAnyAccept ([], [false]) = false ∧ witnessAnyAccept ([], [true]) = true := by
  decide

/-- The unique rejected fixed-length witness is the all-false function. -/
theorem witnessAnyAccept_ofFn_iff (x : List Bool) (n : Nat) (w : Fin n → Bool) :
    witnessAnyAccept (x, List.ofFn w) = true ↔ w ≠ fun _ => false := by
  simp only [witnessAnyAccept, List.any_eq_true, List.mem_ofFn]
  constructor
  · rintro ⟨b, ⟨i, rfl⟩, hb⟩ hw
    simp [hw] at hb
  · intro hw
    by_contra! h
    apply hw
    funext i
    exact Bool.eq_false_iff.mpr (by simpa using h (w i) ⟨i, rfl⟩)

/-- Every witness except the uniquely all-false one accepts. This also handles
length zero, when the unique empty witness rejects. -/
theorem witnessAny_card (x : List Bool) (n : Nat) :
    Fintype.card {w : Fin n → Bool // witnessAnyAccept (x, List.ofFn w) = true} =
      2 ^ n - 1 := by
  classical
  calc
    _ = Fintype.card {w : Fin n → Bool // w ≠ fun _ => false} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (witnessAnyAccept_ofFn_iff x n))
    _ = 2 ^ n - 1 := by rw [Fintype.card_subtype_compl]; simp

/-- The verifier recognizes all nonzero bit vectors of length equal to the
instance length, with a concrete linear-time TM2 and no free padding. -/
noncomputable def nonzeroWitnesses : Complexity.SharpPWitness (encodingList Bool)
    (fun x => 2 ^ x.length - 1) where
  witnessLength := Polynomial.X
  accept := witnessAnyAccept
  verifier := witnessAnyPolyTime
  counts x := by
    calc
      2 ^ x.length - 1 = 2 ^ (Polynomial.X : Polynomial Nat).eval x.length - 1 := by
        rw [Polynomial.eval_X]
      _ = _ := (witnessAny_card x ((Polynomial.X : Polynomial Nat).eval x.length)).symm

/-- A nonconstant counting function with a nonconstant, concretely implemented
polynomial-time verifier belongs to the witness definition of #P. -/
theorem nonzeroWitnesses_inSharpP : Complexity.InSharpP (encodingList Bool)
    (fun x => 2 ^ x.length - 1) := ⟨nonzeroWitnesses⟩

/-- The three shortest lengths have zero, one, and three accepted witnesses. -/
theorem witnessAny_card_boundaries (x : List Bool) :
    Fintype.card {w : Fin 0 → Bool // witnessAnyAccept (x, List.ofFn w) = true} = 0 ∧
    Fintype.card {w : Fin 1 → Bool // witnessAnyAccept (x, List.ofFn w) = true} = 1 ∧
    Fintype.card {w : Fin 2 → Bool // witnessAnyAccept (x, List.ofFn w) = true} = 3 := by
  exact ⟨witnessAny_card x 0, witnessAny_card x 1, witnessAny_card x 2⟩

/-- Instance length changes the number of accepted witnesses. -/
theorem nonzeroWitnesses_nonconstant :
    (2 ^ ([] : List Bool).length - 1 : Nat) ≠ 2 ^ ([false] : List Bool).length - 1 := by
  decide

end Counting.Examples
