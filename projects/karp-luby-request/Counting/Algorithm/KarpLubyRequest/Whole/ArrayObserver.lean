import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.FinEnum

/-!
# An array-backed observer for the original Boolean-stack TM2 syntax

Only the host representation of the stack bank changes. Each primitive reads
the selected address and a push or pop updates exactly that array entry. The
program, labels, finite registers, statement branches and machine transitions
are unchanged. The array is materialized only at the conversion boundary.

This runtime observer is not an algorithm complexity certificate. In
particular, the host cost of the supplied address equivalence is not asserted
to be constant. It does not build or enumerate the machine's register space.
-/

namespace Counting.Algorithm.KarpLubyRequest.Whole.ArrayObserver

open Turing

variable {K L S : Type} {n : ℕ}

/-- A physical array with one word at every address of the fixed stack bank. -/
structure Bank (n : ℕ) where
  words : Array (List Bool)
  size_eq : words.size = n

/-- Addressed read; the size proof is erased by the compiler. -/
def read (e : Fin n ≃ K) (bank : Bank n) (k : K) : List Bool :=
  bank.words[(e.symm k).val]'(by rw [bank.size_eq]; exact (e.symm k).isLt)

/-- Update only the selected stack word, retaining the same bank size. -/
def write (e : Fin n ≃ K) (bank : Bank n) (k : K) (word : List Bool) : Bank n where
  words := bank.words.set (e.symm k).val word
    (by rw [bank.size_eq]; exact (e.symm k).isLt)
  size_eq := by simpa only [Array.size_set] using bank.size_eq

/-- Initial conversion. No transition invokes this whole-bank materialization. -/
def ofStacks (e : Fin n ≃ K) (tapes : K → List Bool) : Bank n where
  words := Array.ofFn (fun i => tapes (e i))
  size_eq := Array.size_ofFn

theorem read_ofStacks (e : Fin n ≃ K) (tapes : K → List Bool) :
    read e (ofStacks e tapes) = tapes := by
  funext k
  simp only [read, ofStacks, Array.getElem_ofFn]
  change tapes (e (e.symm k)) = tapes k
  rw [Equiv.apply_symm_apply]

theorem read_write [DecidableEq K] (e : Fin n ≃ K) (bank : Bank n)
    (k : K) (word : List Bool) :
    read e (write e bank k word) = Function.update (read e bank) k word := by
  funext j
  by_cases h : j = k
  · subst j
    simp only [read, write, Array.getElem_set_self, Function.update_self]
  · have hij : (e.symm k).val ≠ (e.symm j).val := by
      intro hh
      exact h (e.symm.injective (Fin.ext hh)).symm
    simp only [read, write, Function.update_of_ne h]
    exact Array.getElem_set_ne (xs := bank.words) (v := word)
      (by rw [bank.size_eq]; exact (e.symm k).isLt)
      (by rw [bank.size_eq]; exact (e.symm j).isLt) hij

/-- Original control and register values, with an array instead of a stack function. -/
structure Config (n : ℕ) (L S : Type) where
  l : Option L
  var : S
  stk : Bank n

def toCfg (e : Fin n ≃ K) (c : Config n L S) : TM2.Cfg (fun _ : K => Bool) L S :=
  ⟨c.l, c.var, read e c.stk⟩

def ofCfg (e : Fin n ≃ K) (c : TM2.Cfg (fun _ : K => Bool) L S) : Config n L S :=
  ⟨c.l, c.var, ofStacks e c.stk⟩

theorem toCfg_ofCfg (e : Fin n ≃ K) (c : TM2.Cfg (fun _ : K => Bool) L S) :
    toCfg e (ofCfg e c) = c := by
  cases c with
  | mk label state tapes =>
    exact congrArg
      (fun bank : K → List Bool => (⟨label, state, bank⟩ : TM2.Cfg (fun _ : K => Bool) L S))
      (read_ofStacks e tapes)

abbrev Statement (K L S : Type) := TM2.Stmt (fun _ : K => Bool) L S
abbrev Program (K L S : Type) := L → Statement K L S

/-- Direct interpretation of the actual finite statement syntax. -/
def stepAux (e : Fin n ≃ K) : Statement K L S → S → Bank n → Config n L S
  | .push k f q, v, bank => stepAux e q v (write e bank k (f v :: read e bank k))
  | .peek k f q, v, bank => stepAux e q (f v (read e bank k).head?) bank
  | .pop k f q, v, bank =>
      stepAux e q (f v (read e bank k).head?) (write e bank k (read e bank k).tail)
  | .load f q, v, bank => stepAux e q (f v) bank
  | .branch f a b, v, bank => cond (f v) (stepAux e a v bank) (stepAux e b v bank)
  | .goto f, v, bank => ⟨some (f v), v, bank⟩
  | .halt, v, bank => ⟨none, v, bank⟩

theorem stepAux_eq [DecidableEq K] (e : Fin n ≃ K) (q : Statement K L S)
    (v : S) (bank : Bank n) :
    toCfg e (stepAux e q v bank) = TM2.stepAux q v (read e bank) := by
  induction q generalizing v bank with
  | push k f q ih =>
    simpa only [stepAux, TM2.stepAux, read_write] using
      (ih v (write e bank k (f v :: read e bank k)))
  | peek k f q ih => exact ih (f v (read e bank k).head?) bank
  | pop k f q ih =>
    simpa only [stepAux, TM2.stepAux, read_write] using
      (ih (f v (read e bank k).head?) (write e bank k (read e bank k).tail))
  | load f q ih => exact ih (f v) bank
  | branch f a b ha hb =>
    cases h : f v <;> simp only [stepAux, TM2.stepAux, h, cond_false, cond_true, ha, hb]
  | goto f => rfl
  | halt => rfl

/-- One original TM2 transition. Halted configurations produce `none`. -/
def step (e : Fin n ≃ K) (program : Program K L S) :
    Config n L S → Option (Config n L S)
  | ⟨none, _, _⟩ => none
  | ⟨some label, v, bank⟩ => some (stepAux e (program label) v bank)

theorem step_eq [DecidableEq K] (e : Fin n ≃ K) (program : Program K L S)
    (c : Config n L S) :
    (step e program c).map (toCfg e) = TM2.step program (toCfg e c) := by
  cases c with
  | mk label state bank =>
    cases label with
    | none => rfl
    | some label => exact congrArg some (stepAux_eq e (program label) state bank)

/-- Optional configurations commute with the same single transition as well. -/
theorem bind_step_eq [DecidableEq K] (e : Fin n ≃ K) (program : Program K L S)
    (c : Option (Config n L S)) :
    (c.bind (step e program)).map (toCfg e) =
      (c.map (toCfg e)).bind (TM2.step program) := by
  cases c with
  | none => rfl
  | some c => exact step_eq e program c

end Counting.Algorithm.KarpLubyRequest.Whole.ArrayObserver
