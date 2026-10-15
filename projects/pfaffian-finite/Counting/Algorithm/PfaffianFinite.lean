import Counting.FiniteSupport.F1
import Counting.Algorithm.Pfaffian.Evaluator
import Counting.Algorithm.Pfaffian.FiniteAlphabet

/-!
# A finite-stack machine for the complete Pfaffian row evaluator

The existing evaluator proves existence of a concrete timed TM2 program. We fix
one such source witness, then compile that program to its finite symbol support.
No finiteness claim is made about the original scratch types. The new machine
has an exact transition-erasure simulation, and retains the source external
codecs, execution counts, and time polynomial.
-/

noncomputable section

namespace Counting.Algorithm.PfaffianFinite

open Turing
open Counting.Algorithm.Pfaffian

/-- The finite-support compiler produces the existing A1 certificate structure.
This can be consumed directly by `Counting.Adapters.Pfaffian.toPolyTime`. -/
def refine {α β Γ₀ Γ₁ : Type} [Fintype Γ₁]
    {ea : α → List Γ₀} {eb : β → List Γ₁} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) : FiniteComputer ea eb f where
  toTM2ComputableInPolyTime := Counting.Computation.FiniteSupport.computer h
  finiteAlphabets := Counting.Computation.FiniteSupport.computerCertificate h

variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}

/-- Fix the actual source witness supplied by the original complete evaluator.
The field basis is fixed; matrix order remains part of the encoded input. -/
def sourceComputer (basis : Module.Basis (Fin dimension) ℚ K) :
    TM2ComputableInPolyTime (gridEncoding basis).encode
      (PfaffianPort.Complexity.numberFieldEncoding basis).encode (evaluateGrid (K := K)) :=
  Classical.choice (fp_evaluateGrid basis)

/-- The complete evaluator, with a proved finite alphabet on every actual stack
of the refined machine. Input/output code functions are literally unchanged. -/
def evaluateGridComputer (basis : Module.Basis (Fin dimension) ℚ K) :
    FiniteComputer (gridEncoding basis).encode
      (PfaffianPort.Complexity.numberFieldEncoding basis).encode (evaluateGrid (K := K)) :=
  refine (sourceComputer basis)

/-- The same certified machine under F1's faithful-codec interface. -/
def evaluateGridPolyTime (basis : Module.Basis (Fin dimension) ℚ K) :
    Counting.Computation.PolyTime (gridEncoding basis).toFinEncoding
      (PfaffianPort.Complexity.numberFieldEncoding basis).toFinEncoding
      (evaluateGrid (K := K)) :=
  Counting.Computation.FiniteSupport.toPolyTime (sourceComputer basis)

/-- Both packaging interfaces retain the identical refined timed computer. -/
theorem evaluateGridPolyTime_computer (basis : Module.Basis (Fin dimension) ℚ K) :
    (evaluateGridPolyTime basis).toTM2ComputableInPolyTime =
      (evaluateGridComputer basis).toTM2ComputableInPolyTime := rfl

/-- The original polynomial is retained without any alphabet-conversion charge. -/
@[simp] theorem evaluateGridComputer_time (basis : Module.Basis (Fin dimension) ℚ K) :
    (evaluateGridComputer basis).time = (sourceComputer basis).time := rfl

/-- Every encoded execution retains its exact source transition count. -/
@[simp] theorem evaluateGridComputer_steps (basis : Module.Basis (Fin dimension) ℚ K)
    (g : Grid K) :
    ((evaluateGridComputer basis).outputsFun g).steps =
      ((sourceComputer basis).outputsFun g).steps := rfl

@[simp] theorem evaluateGridPolyTime_time (basis : Module.Basis (Fin dimension) ℚ K) :
    (evaluateGridPolyTime basis).time = (sourceComputer basis).time := rfl

@[simp] theorem evaluateGridPolyTime_steps (basis : Module.Basis (Fin dimension) ℚ K)
    (g : Grid K) :
    ((evaluateGridPolyTime basis).outputsFun g).steps =
      ((sourceComputer basis).outputsFun g).steps := rfl

/-- The refined Pfaffian machine simulates each original program transition
exactly by erasing symbol-support proofs. -/
theorem evaluateGridComputer_erase_step (basis : Module.Basis (Fin dimension) ℚ K)
    (c : (evaluateGridComputer basis).tm.Cfg) :
    Option.map (Counting.Computation.FiniteSupport.eraseComputerCfg (sourceComputer basis))
        ((evaluateGridComputer basis).tm.step c) =
      (sourceComputer basis).tm.step (Counting.Computation.FiniteSupport.eraseComputerCfg (sourceComputer basis) c) :=
  Counting.Computation.FiniteSupport.computer_erase_step (sourceComputer basis) c

/-- Full F1 membership for varying matrix order over the fixed represented field. -/
theorem evaluateGrid_inFP (basis : Module.Basis (Fin dimension) ℚ K) :
    Counting.Computation.InFP (gridEncoding basis).toFinEncoding
      (PfaffianPort.Complexity.numberFieldEncoding basis).toFinEncoding
      (evaluateGrid (K := K)) :=
  ⟨evaluateGridPolyTime basis⟩

/-- The finite-machine endpoint and the existing independent signed-pairing
correctness theorem, including empty and odd orders. -/
theorem certified_evaluateGrid (basis : Module.Basis (Fin dimension) ℚ K) :
    Counting.Computation.InFP (gridEncoding basis).toFinEncoding
      (PfaffianPort.Complexity.numberFieldEncoding basis).toFinEncoding
      (evaluateGrid (K := K)) ∧
    ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
      (∀ i j, A j i = -A i j) → (∀ i, A i i = 0) →
      evaluateGrid (matrixRows A) = pairingPfaffian A :=
  ⟨evaluateGrid_inFP basis, fun A hs hd => evaluateGrid_eq_pairingPfaffian A hs hd⟩

end Counting.Algorithm.PfaffianFinite
