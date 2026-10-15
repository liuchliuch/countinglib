import Counting.Algorithm.VariableEliminationLayout.FinRange
import Counting.Algorithm.VariableEliminationLayout.Reader

/-! # Complete primitive preprocessing for finite-ordinal layouts -/

namespace Counting.Algorithm.VariableEliminationLayout

open Counting.Algorithm.VariableElimination

/-- The generated lists themselves are used to build the layout. The public
constructor asks only for sizes, not for a caller-supplied enumeration proof. -/
structure FinLayoutPreparation (n q : Nat) where
  layout : TableLayout (Fin n) (Fin q)
  coordinateGeneration : FinRangeCost
  colourGeneration : FinRangeCost
  layoutConstructions : Nat

/-- Both lists are generated once. Their canonical order is known from generation,
so this specialized preparation performs no sort and no length traversal. -/
def prepareFinLayout (n q : Nat) : FinLayoutPreparation n q :=
  let xs := generateFinRange n
  let ds := generateFinRange q
  ⟨⟨xs.values, ds.values, q, by simp [xs], by simp [ds], by simp [ds]⟩,
    xs.cost, ds.cost, 1⟩

@[simp] theorem coordinateGeneration_prepareFinLayout (n q : Nat) :
    (prepareFinLayout n q).coordinateGeneration = ⟨n, n + 1, n, 0, 1⟩ := by
  simp [prepareFinLayout]

@[simp] theorem colourGeneration_prepareFinLayout (n q : Nat) :
    (prepareFinLayout n q).colourGeneration = ⟨q, q + 1, q, 0, 1⟩ := by
  simp [prepareFinLayout]

@[simp] theorem layoutConstructions_prepareFinLayout (n q : Nat) :
    (prepareFinLayout n q).layoutConstructions = 1 := rfl

/-- A prepared wrapper shares the old array; it does not copy or retabulate rows. -/
structure FinCachePreparation (n q : Nat) (R : Type) where
  cache : CachedTable (Fin n) (Fin q) R
  preparation : FinLayoutPreparation n q
  cacheConstructions : Nat

def cacheFinTable {n q : Nat} {R : Type} (t : DenseTable (Fin n) (Fin q) R) :
    FinCachePreparation n q R :=
  let prepared := prepareFinLayout n q
  ⟨⟨t, prepared.layout⟩, prepared, 1⟩

@[simp] theorem preparation_cacheFinTable {n q : Nat} {R : Type}
    (t : DenseTable (Fin n) (Fin q) R) :
    (cacheFinTable t).preparation = prepareFinLayout n q := rfl

@[simp] theorem table_cacheFinTable {n q : Nat} {R : Type}
    (t : DenseTable (Fin n) (Fin q) R) : (cacheFinTable t).cache.table = t := rfl

@[simp] theorem constructions_cacheFinTable {n q : Nat} {R : Type}
    (t : DenseTable (Fin n) (Fin q) R) : (cacheFinTable t).cacheConstructions = 1 := rfl

theorem evalFin_cacheFinTable {n q : Nat} {R : Type}
    (t : DenseTable (Fin n) (Fin q) R) (a : Fin n → Fin q) :
    (cacheFinTable t).cache.evalFin a = t.eval a := by
  rw [CachedTable.evalFin_eq_eval, CachedTable.eval_eq_legacy, table_cacheFinTable]

end Counting.Algorithm.VariableEliminationLayout
