import Counting.Computation.PolyTime
import Counting.Algorithm.Pfaffian.FiniteAlphabet
import Counting.Algorithm.PfaffianFinite

/-!
# Faithful-codec bridge for certified Pfaffian machine components

The two structures describe the same timed computer once faithful encodings and
all-stack finite-alphabet certificates are present. Conversion retains the exact
machine, its time polynomial and each execution. The finite-support compiler now
supplies such a refined machine for the full evaluator; the bridges below prove
that its existing A1 certificate and public F1 endpoint are identical packages.
-/

namespace Counting.Adapters.Pfaffian

open Counting.Algorithm.Pfaffian

variable {α β Γ₀ Γ₁ : Type} [Fintype Γ₀] [Fintype Γ₁]
    {ea : Computability.Encoding α Γ₀} {eb : Computability.Encoding β Γ₁}
    {f : α → β}

/-- Package an actually certified timed witness in the shared machine interface. -/
def toPolyTime (computer : FiniteComputer ea.encode eb.encode f) :
    Counting.Computation.PolyTime ea eb f where
  toTM2ComputableInPolyTime := computer.toTM2ComputableInPolyTime
  finiteAlphabets := computer.finiteAlphabets

/-- The common machine interface also supplies the algorithm component contract. -/
def ofPolyTime (computer : Counting.Computation.PolyTime ea eb f) :
    FiniteComputer ea.encode eb.encode f where
  toTM2ComputableInPolyTime := computer.toTM2ComputableInPolyTime
  finiteAlphabets := computer.finiteAlphabets

@[simp] theorem toPolyTime_ofPolyTime (computer : Counting.Computation.PolyTime ea eb f) :
    toPolyTime (ofPolyTime computer) = computer := by
  cases computer
  rfl

@[simp] theorem ofPolyTime_toPolyTime (computer : FiniteComputer ea.encode eb.encode f) :
    ofPolyTime (toPolyTime computer) = computer := by
  cases computer
  rfl

@[simp] theorem toPolyTime_machine (computer : FiniteComputer ea.encode eb.encode f) :
    (toPolyTime computer).tm = computer.tm := rfl

@[simp] theorem toPolyTime_time (computer : FiniteComputer ea.encode eb.encode f) :
    (toPolyTime computer).time = computer.time := rfl

@[simp] theorem toPolyTime_steps (computer : FiniteComputer ea.encode eb.encode f) (a : α) :
    ((toPolyTime computer).outputsFun a).steps = (computer.outputsFun a).steps := rfl

/-- Existence is transported only from a witness with all required certificates. -/
theorem inFP_of_finiteComputer (computer : FiniteComputer ea.encode eb.encode f) :
    Counting.Computation.InFP ea eb f := ⟨toPolyTime computer⟩

/-- Refining a raw timed computer and using the original adapter gives the same
F1 witness as the finite-support compiler's direct public endpoint. -/
@[simp] theorem toPolyTime_refine
    (computer : Turing.TM2ComputableInPolyTime ea.encode eb.encode f) :
    toPolyTime (Counting.Algorithm.PfaffianFinite.refine computer) =
      Counting.Computation.FiniteSupport.toPolyTime computer := rfl

/-- The complete varying-order evaluator passes through the existing adapter
without changing its refined machine, certificate, encodings, or time bound. -/
@[simp] theorem toPolyTime_evaluateGridComputer
    {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) :
    toPolyTime (Counting.Algorithm.PfaffianFinite.evaluateGridComputer basis) =
      Counting.Algorithm.PfaffianFinite.evaluateGridPolyTime basis := rfl

end Counting.Adapters.Pfaffian
