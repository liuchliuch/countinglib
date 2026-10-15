import Counting.Algorithm.VariableEliminationLayout.Layout
import Counting.Algorithm.VariableElimination.Table

/-!
# Counted cached table reads

All coordinate and colour lists are shared from the prepared layout. The code
contains no sorting or enumeration. Search increments are actual natural-number
additions, and are recorded separately from the Horner additions/multiplications.
-/

namespace Counting.Algorithm.VariableEliminationLayout

universe u v w

open Counting.Algorithm.VariableElimination

structure DigitResult where
  value : Nat
  comparisons : Nat
  listCases : Nat
  increments : Nat
  deriving Repr, DecidableEq

/-- Linear lookup counting the actual unsuccessful-search index increments. -/
def searchCounted {D : Type v} [DecidableEq D] (d : D) : List D → DigitResult
  | [] => ⟨0, 0, 1, 0⟩
  | c :: cs =>
      if c = d then ⟨0, 1, 1, 0⟩
      else
        let t := searchCounted d cs
        ⟨t.value + 1, t.comparisons + 1, t.listCases + 1, t.increments + 1⟩

@[simp] theorem value_searchCounted {D : Type v} [DecidableEq D]
    (d : D) (ds : List D) : (searchCounted d ds).value = ds.idxOf d := by
  induction ds with
  | nil => rfl
  | cons c cs ih =>
      by_cases h : c = d
      · subst c; simp [searchCounted]
      · simp [searchCounted, h, ih, List.idxOf_cons_ne cs h]

@[simp] theorem increments_searchCounted {D : Type v} [DecidableEq D]
    (d : D) (ds : List D) : (searchCounted d ds).increments = ds.idxOf d := by
  induction ds with
  | nil => rfl
  | cons c cs ih =>
      by_cases h : c = d
      · subst c; simp [searchCounted]
      · simp [searchCounted, h, ih, List.idxOf_cons_ne cs h]

theorem comparisons_searchCounted {D : Type v} [DecidableEq D]
    (d : D) (ds : List D) (h : d ∈ ds) :
    (searchCounted d ds).comparisons = ds.idxOf d + 1 := by
  induction ds with
  | nil => simp at h
  | cons c cs ih =>
      by_cases he : c = d
      · subst c; simp [searchCounted]
      · have ht : d ∈ cs := by simpa [Ne.symm he] using h
        simp [searchCounted, he, ih ht, List.idxOf_cons_ne cs he]

theorem cases_searchCounted {D : Type v} [DecidableEq D]
    (d : D) (ds : List D) (h : d ∈ ds) :
    (searchCounted d ds).listCases = ds.idxOf d + 1 := by
  induction ds with
  | nil => simp at h
  | cons c cs ih =>
      by_cases he : c = d
      · subst c; simp [searchCounted]
      · have ht : d ∈ cs := by simpa [Ne.symm he] using h
        simp [searchCounted, he, ih ht, List.idxOf_cons_ne cs he]

/-- Reader operations exclude preprocessing, coefficient operations, and the
instrumentation's counter bookkeeping. The reader's own body constructs no
list cells; work internal to a supplied assignment function is outside these counters. -/
structure ReadWork where
  coordinateCases : Nat
  colourCases : Nat
  colourComparisons : Nat
  indexIncrements : Nat
  hornerAdditions : Nat
  hornerMultiplications : Nat
  arrayReads : Nat
  deriving Repr, DecidableEq

structure AddressResult where
  value : Nat
  work : ReadWork
  deriving Repr

/-- Each actual coordinate step computes its digit once, then multiplies and
adds once. The suffix recursion receives that computed accumulator. -/
def addressLoop {α : Type u} (q : Nat) (digit : α → DigitResult) :
    List α → Nat → AddressResult
  | [], acc => ⟨acc, ⟨1, 0, 0, 0, 0, 0, 0⟩⟩
  | x :: xs, acc =>
      let d := digit x
      let t := addressLoop q digit xs (acc * q + d.value)
      ⟨t.value, ⟨t.work.coordinateCases + 1,
        t.work.colourCases + d.listCases,
        t.work.colourComparisons + d.comparisons,
        t.work.indexIncrements + d.increments,
        t.work.hornerAdditions + 1, t.work.hornerMultiplications + 1, 0⟩⟩

@[simp] theorem value_addressLoop {α : Type u} (q : Nat) (digit : α → DigitResult)
    (xs : List α) (acc : Nat) :
    (addressLoop q digit xs acc).value =
      xs.foldl (fun n x => n * q + (digit x).value) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [addressLoop, ih]

/-- Closed componentwise count, derived from the address recursion. -/
theorem work_addressLoop {α : Type u} (q : Nat) (digit : α → DigitResult)
    (xs : List α) (acc : Nat) :
    (addressLoop q digit xs acc).work =
      ⟨xs.length + 1, (xs.map (fun x => (digit x).listCases)).sum,
        (xs.map (fun x => (digit x).comparisons)).sum,
        (xs.map (fun x => (digit x).increments)).sum,
        xs.length, xs.length, 0⟩ := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [addressLoop, ih, Nat.add_comm]

namespace TableLayout

variable {α : Type u} {D : Type v}
variable [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D]

/-- Address with no preprocessing calls; the prepared lists are reused. -/
def address (l : TableLayout α D) (a : α → D) : AddressResult :=
  addressLoop l.radix (fun x => searchCounted (a x) l.colours) l.coordinates 0

@[simp] theorem value_address (l : TableLayout α D) (a : α → D) :
    (l.address a).value = l.index a := by simp [address, index, hornerIndex]

theorem work_address (l : TableLayout α D) (a : α → D) :
    (l.address a).work =
      ⟨Fintype.card α + 1,
        (l.coordinates.map (fun x => l.colours.idxOf (a x) + 1)).sum,
        (l.coordinates.map (fun x => l.colours.idxOf (a x) + 1)).sum,
        (l.coordinates.map (fun x => l.colours.idxOf (a x))).sum,
        Fintype.card α, Fintype.card α, 0⟩ := by
  have hm (x : α) : a x ∈ l.colours := by rw [l.colours_eq]; simp
  simp [address, work_addressLoop, comparisons_searchCounted _ _ (hm _),
    cases_searchCounted _ _ (hm _)]

/-- Fin digits bypass the stored colour list entirely. -/
def addressFin {q : Nat} (l : TableLayout α (Fin q)) (a : α → Fin q) : AddressResult :=
  addressLoop q (fun x => ⟨(a x).val, 0, 0, 0⟩) l.coordinates 0

@[simp] theorem value_addressFin {q : Nat} (l : TableLayout α (Fin q))
    (a : α → Fin q) : (l.addressFin a).value = l.indexFin a := by
  simp [addressFin, indexFin, hornerIndex]

theorem work_addressFin {q : Nat} (l : TableLayout α (Fin q)) (a : α → Fin q) :
    (l.addressFin a).work = ⟨Fintype.card α + 1, 0, 0, 0,
      Fintype.card α, Fintype.card α, 0⟩ := by
  simp [addressFin, work_addressLoop]

end TableLayout

/-- Wrap an arbitrary existing array with a prepared, reusable layout. -/
structure CachedTable (α : Type u) (D : Type v) (R : Type w)
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D] where
  table : DenseTable α D R
  layout : TableLayout α D

structure ReadResult (R : Type w) where
  value : R
  work : ReadWork

namespace CachedTable

variable {α : Type u} {D : Type v} {R : Type w}
variable [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D]

/-- Compute the cached address and perform its single actual array read. -/
def read (t : CachedTable α D R) (a : α → D) : ReadResult R :=
  let i := t.layout.address a
  let value := t.table.values[i.value]'(by
    rw [t.table.size_values, TableLayout.value_address]
    exact t.layout.index_lt a)
  ⟨value, { i.work with arrayReads := 1 }⟩

/-- This callback is installed on actual cached factors. -/
def eval (t : CachedTable α D R) (a : α → D) : R := (t.read a).value

theorem eval_eq_evalIndexed (t : CachedTable α D R) (a : α → D) :
    t.eval a = t.table.evalIndexed a := by
  simp only [eval, read, TableLayout.value_address, TableLayout.index_eq_assignmentIndex,
    DenseTable.evalIndexed]

theorem eval_eq_legacy (t : CachedTable α D R) (a : α → D) :
    t.eval a = t.table.eval a := by
  rw [eval_eq_evalIndexed, DenseTable.evalIndexed_eq_eval]

@[simp] theorem work_read (t : CachedTable α D R) (a : α → D) :
    (t.read a).work = { (t.layout.address a).work with arrayReads := 1 } := rfl

/-- Specialized actual reader, with its colour-search-free address installed. -/
def readFin {q : Nat} (t : CachedTable α (Fin q) R) (a : α → Fin q) : ReadResult R :=
  let i := t.layout.addressFin a
  let value := t.table.values[i.value]'(by
    rw [t.table.size_values, TableLayout.value_addressFin, TableLayout.indexFin_eq_index]
    exact t.layout.index_lt a)
  ⟨value, { i.work with arrayReads := 1 }⟩

def evalFin {q : Nat} (t : CachedTable α (Fin q) R) (a : α → Fin q) : R :=
  (t.readFin a).value

theorem evalFin_eq_eval {q : Nat} (t : CachedTable α (Fin q) R) (a : α → Fin q) :
    t.evalFin a = t.eval a := by
  simp only [evalFin, readFin, eval, read, TableLayout.value_addressFin,
    TableLayout.value_address, TableLayout.indexFin_eq_index]

@[simp] theorem work_readFin {q : Nat} (t : CachedTable α (Fin q) R) (a : α → Fin q) :
    (t.readFin a).work =
      ⟨Fintype.card α + 1, 0, 0, 0, Fintype.card α, Fintype.card α, 1⟩ := by
  simp only [readFin, TableLayout.work_addressFin]

end CachedTable

end Counting.Algorithm.VariableEliminationLayout
