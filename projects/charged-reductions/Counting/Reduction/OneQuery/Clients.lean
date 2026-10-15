import Counting.Reduction.OneQuery.Composition
import PlanarHom.ArithmeticCircuitPrimitives

/-! # Concrete nonidentity, zero-answer and empty-input clients -/

noncomputable section
namespace Counting.Reduction.OneQuery.Clients
open PlanarHom.Complexity Counting.Computation Counting.Complexity
open Counting.Bridge.PlanarHomSharpP

private theorem zero_code : BitEncoding.nat.encode 0 = [] := rfl
private theorem one_code : BitEncoding.nat.encode 1 = [true] := rfl

/-- Reuse the source's unary program and step theorem, with the concrete step
field exposed before any dependent transport of the bounded-run record. -/
def flipComputer : Turing.TM2ComputableInPolyTime BitEncoding.bool.encode
    BitEncoding.bool.encode Bool.not where
  tm := PlanarHom.ArithmeticCircuitPrimitives.unaryMachine BitEncoding.bool Bool.not
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun b := {
    steps := 1
    evals_in_steps := by
      change (PlanarHom.ArithmeticCircuitPrimitives.unaryMachine BitEncoding.bool Bool.not).step
        (Turing.initList _ [b]) = some (Turing.haltList _ [!b])
      exact PlanarHom.ArithmeticCircuitPrimitives.unary_step BitEncoding.bool Bool.not b
    steps_le_m := by simp only [Polynomial.eval_one, le_refl] }

/-- The map flips the bit, while the nonconstant target count swaps zero and one. -/
def complement : ParsimoniousReduction BitEncoding.bool.toFinEncoding
    BitEncoding.bool.toFinEncoding (fun b => if b then 0 else 1)
      (fun b => if b then 1 else 0) where
  map := Bool.not
  machine := finiteComputer flipComputer
  correct b := by cases b <;> rfl

theorem complement_not_identity : complement.map false ≠ false := by decide

def complementCharged : PromisePolyTimeTuringReduction
    (problem BitEncoding.bool (fun b => if b then 0 else 1))
    (problem BitEncoding.bool (fun b => if b then 1 else 0)) :=
  compile complement 1 (fun b => by
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, zero_code, one_code,
      List.length_nil, List.length_singleton, Polynomial.eval_one] <;> decide)

/-- The physical flip costs one transition; the query costs two transitions
and the materialized one-bit query and one-bit answer are both charged. -/
theorem complement_exact_run :
    (machine complement).Run (problem BitEncoding.bool (fun b => if b then 1 else 0)).value
      ((machine complement).initial [false]) ((machine complement).final [true])
      3 5 [([true], [true])] := by
  have h := run_correct complement _ (fun _ _ => rfl) false
  have hs : (complement.machine.outputsFun false).steps = 1 := rfl
  have hm : complement.map false = true := rfl
  rw [hs] at h
  simpa only [hm, BitEncoding.bool, Bool.false_eq_true,
    ite_false, ite_true, one_code, List.length_singleton] using h

/-- Clear arbitrary input to the empty query; the count is genuinely zero. -/
def erase : ParsimoniousReduction BitEncoding.bits.toFinEncoding
    BitEncoding.bits.toFinEncoding (fun _ => 0) (fun _ => 0) where
  map _ := []
  machine := finiteComputer (PlanarHom.ConstantMachines.computer
    BitEncoding.bits BitEncoding.bits [])
  correct _ := rfl

def zeroCharged := erase.toCharged (noWitnesses BitEncoding.bits.toFinEncoding)

theorem erase_exact_run (input : Bits) :
    (machine erase).Run (problem BitEncoding.bits (fun _ => 0)).value
      ((machine erase).initial input) ((machine erase).final [])
      (input.length + 3) (input.length + 3) [([], [])] := by
  have h := run_correct erase _ (fun _ _ => rfl) input
  have hs : (erase.machine.outputsFun input).steps = input.length + 1 := rfl
  have hm : erase.map input = [] := rfl
  rw [hs] at h
  simpa only [hm, BitEncoding.bits, id_eq, zero_code, List.length_nil,
    Nat.add_zero, Nat.add_assoc] using h

theorem empty_input_exact_run :
    zeroCharged.machine.Run (problem BitEncoding.bits (fun _ => 0)).value
      (zeroCharged.machine.initial []) (zeroCharged.machine.final []) 3 3 [([], [])] :=
  erase_exact_run []

/-- Actual nested-query composition: clear once before invoking the second
charged clear-and-query reduction. This is the provider's `trans`, not a map law. -/
def twiceErased := chain erase (noWitnesses BitEncoding.bits.toFinEncoding) zeroCharged

/-- The final oracle can be eliminated by a real input-clearing constant machine. -/
def zeroSolver : PolyTime BitEncoding.bits.toFinEncoding BitEncoding.nat.toFinEncoding
    (fun _ => 0) := finiteComputer (PlanarHom.ConstantMachines.computer
      BitEncoding.bits BitEncoding.nat 0)

def twiceErasedComputer := substitute erase (noWitnesses BitEncoding.bits.toFinEncoding)
  zeroCharged (canonicalSolver zeroSolver)

/-- The finite-alphabet compiler preserves the substitution program's words,
polynomial and exact step witnesses. -/
def twiceErasedFinite := finiteComputer twiceErasedComputer

def twiceErased_output (input : Bits) :
    Turing.TM2OutputsInTime twiceErasedFinite.tm
      (input.map twiceErasedFinite.inputAlphabet.symm)
      (some ([].map twiceErasedFinite.outputAlphabet.symm))
      (twiceErasedFinite.time.eval input.length) := by
  have h := twiceErasedFinite.outputsFun ⟨input, valid_encode BitEncoding.bits (fun _ => 0) input⟩
  have hv : (problem BitEncoding.bits (fun _ => 0)).value input = [] :=
    (value_encode BitEncoding.bits (fun _ => 0) input).trans zero_code
  change Turing.TM2OutputsInTime twiceErasedFinite.tm
    (input.map twiceErasedFinite.inputAlphabet.invFun)
    (some (((problem BitEncoding.bits (fun _ => 0)).value input).map
      twiceErasedFinite.outputAlphabet.invFun))
    (twiceErasedFinite.time.eval input.length) at h
  rw [hv] at h
  simpa only [Equiv.invFun_as_coe] using h


/-- Even an exponentially large count has a linear encoded answer-size bound;
no algorithm for evaluating that count is passed to the charged compiler. -/
def exponentialCharged :=
  (ParsimoniousReduction.refl BitEncoding.bits.toFinEncoding
    (fun x => 2 ^ x.length)).toCharged
      (by
        have h := allWitnesses BitEncoding.bits.toFinEncoding Polynomial.X
        dsimp only [BitEncoding.toFinEncoding, BitEncoding.bits] at h ⊢
        simpa only [id_eq, Polynomial.eval_X] using h)

end Counting.Reduction.OneQuery.Clients
