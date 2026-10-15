import Counting.Algorithm.VariableEliminationLayout.Batch

/-!
# Compositional observations from executed operations

Counters describe logical source operations, not physical allocation or bit cost.
Counter bookkeeping and erased proofs are excluded. Oracle calls are explicit;
the implementation inside an arbitrary input coefficient callback is not charged
as if it were one machine instruction.
-/

namespace Counting.Algorithm.VariableEliminationWork

open Counting.Algorithm.VariableEliminationLayout

/-- Separate coefficient, address, list, construction, and input-oracle observations. -/
@[ext] structure Work where
  reads : ReadWork := ReadWork.zero
  coefficientAdditions : Nat := 0
  coefficientMultiplications : Nat := 0
  oracleCalls : Nat := 0
  listCases : Nat := 0
  listCons : Nat := 0
  nilResults : Nat := 0
  arrayPushes : Nat := 0
  arrayConstructions : Nat := 0
  natIncrements : Nat := 0
  generationTests : Nat := 0
  layoutConstructions : Nat := 0
  cacheConstructions : Nat := 0
  closureConstructions : Nat := 0
  deriving DecidableEq, Repr

namespace Work

def zero : Work := {}

def add (a b : Work) : Work where
  reads := a.reads.add b.reads
  coefficientAdditions := a.coefficientAdditions + b.coefficientAdditions
  coefficientMultiplications := a.coefficientMultiplications + b.coefficientMultiplications
  oracleCalls := a.oracleCalls + b.oracleCalls
  listCases := a.listCases + b.listCases
  listCons := a.listCons + b.listCons
  nilResults := a.nilResults + b.nilResults
  arrayPushes := a.arrayPushes + b.arrayPushes
  arrayConstructions := a.arrayConstructions + b.arrayConstructions
  natIncrements := a.natIncrements + b.natIncrements
  generationTests := a.generationTests + b.generationTests
  layoutConstructions := a.layoutConstructions + b.layoutConstructions
  cacheConstructions := a.cacheConstructions + b.cacheConstructions
  closureConstructions := a.closureConstructions + b.closureConstructions

@[simp] theorem zero_add (a : Work) : zero.add a = a := by
  cases a with
  | mk reads _ _ _ _ _ _ _ _ _ _ _ _ _ => cases reads; simp [zero, add, ReadWork.zero, ReadWork.add]

@[simp] theorem add_zero (a : Work) : a.add zero = a := by
  cases a with
  | mk reads _ _ _ _ _ _ _ _ _ _ _ _ _ => cases reads; simp [zero, add, ReadWork.zero, ReadWork.add]

theorem add_assoc (a b c : Work) : (a.add b).add c = a.add (b.add c) := by
  cases a; cases b; cases c
  simp only [add, ReadWork.add, Nat.add_assoc]

def sum : List Work → Work
  | [] => zero
  | x :: xs => x.add (sum xs)

@[simp] theorem sum_append (xs ys : List Work) : sum (xs ++ ys) = (sum xs).add (sum ys) := by
  induction xs <;> simp [sum, *, add_assoc]

/-- Preserve every actual field of a range-generation observation. -/
def ofRange (w : FinRangeCost) : Work where
  listCons := w.listCons
  generationTests := w.loopTests
  natIncrements := w.natIncrements
  listCases := w.listTraversals
  nilResults := w.nilResults

def ofCachePreparation {n q : Nat} {R : Type} (p : FinCachePreparation n q R) : Work :=
  (ofRange p.preparation.coordinateGeneration).add
    ((ofRange p.preparation.colourGeneration).add
      {layoutConstructions := p.preparation.layoutConstructions,
       cacheConstructions := p.cacheConstructions})

end Work

/-- A returned value and observations accumulated while computing it. -/
structure Observed (A : Type) where
  value : A
  work : Work
  deriving Repr

namespace Observed

variable {A R : Type}

def pure (a : A) : Observed A := ⟨a, Work.zero⟩

/-- This recursion invokes the reader once per list element and multiplies the
returned coefficient once. It does not precompute a list of unobserved values. -/
def product [MulOneClass R] (reader : A → Observed R) : List A → Observed R
  | [] => ⟨1, {listCases := 1}⟩
  | a :: xs =>
      let first := reader a
      let tail := product reader xs
      ⟨first.value * tail.value,
        first.work.add (tail.work.add {coefficientMultiplications := 1, listCases := 1})⟩

def sum [AddZeroClass R] (reader : A → Observed R) : List A → Observed R
  | [] => ⟨0, {listCases := 1}⟩
  | a :: xs =>
      let first := reader a
      let tail := sum reader xs
      ⟨first.value + tail.value,
        first.work.add (tail.work.add {coefficientAdditions := 1, listCases := 1})⟩

@[simp] theorem value_product [MulOneClass R] (reader : A → Observed R) (xs : List A) :
    (product reader xs).value = (xs.map (fun a => (reader a).value)).prod := by
  induction xs <;> simp [product, *]

@[simp] theorem value_sum [AddZeroClass R] (reader : A → Observed R) (xs : List A) :
    (sum reader xs).value = (xs.map (fun a => (reader a).value)).sum := by
  induction xs <;> simp [sum, *]

theorem work_product [MulOneClass R] (reader : A → Observed R) (xs : List A) :
    (product reader xs).work =
      (Work.sum (xs.map (fun a => (reader a).work))).add
        {coefficientMultiplications := xs.length, listCases := xs.length + 1} := by
  induction xs with
  | nil => simp [product, Work.sum]
  | cons a xs ih =>
      simp only [product, ih, List.map_cons, Work.sum, List.length_cons, Work.add_assoc]
      congr 1

theorem work_sum [AddZeroClass R] (reader : A → Observed R) (xs : List A) :
    (sum reader xs).work =
      (Work.sum (xs.map (fun a => (reader a).work))).add
        {coefficientAdditions := xs.length, listCases := xs.length + 1} := by
  induction xs with
  | nil => simp [sum, Work.sum]
  | cons a xs ih =>
      simp only [sum, ih, List.map_cons, Work.sum, List.length_cons, Work.add_assoc]
      congr 1

end Observed
end Counting.Algorithm.VariableEliminationWork
