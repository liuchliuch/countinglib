import Counting.Algorithm.VariableEliminationLayout.FinPreparation

/-!
# One preparation followed by repeated cached reads

The same cached table is passed unchanged to every recursive call. The batch
records all reader operations plus its own input-list cases and output conses.
-/

namespace Counting.Algorithm.VariableEliminationLayout

universe u v w

namespace ReadWork

def zero : ReadWork := ⟨0, 0, 0, 0, 0, 0, 0⟩

def add (a b : ReadWork) : ReadWork :=
  ⟨a.coordinateCases + b.coordinateCases, a.colourCases + b.colourCases,
    a.colourComparisons + b.colourComparisons, a.indexIncrements + b.indexIncrements,
    a.hornerAdditions + b.hornerAdditions,
    a.hornerMultiplications + b.hornerMultiplications, a.arrayReads + b.arrayReads⟩

def sum : List ReadWork → ReadWork
  | [] => zero
  | x :: xs => x.add (sum xs)

end ReadWork

structure BatchResult (R : Type w) where
  values : List R
  reads : ReadWork
  assignmentListCases : Nat
  outputCons : Nat

/-- Execute a supplied reader on each listed assignment, charging the batch's
own traversal and output-cell construction as well as the reader work. -/
def readBatch {A : Type u} {R : Type w} (reader : A → ReadResult R) :
    List A → BatchResult R
  | [] => ⟨[], ReadWork.zero, 1, 0⟩
  | a :: assignments =>
      let first := reader a
      let rest := readBatch reader assignments
      ⟨first.value :: rest.values, first.work.add rest.reads,
        rest.assignmentListCases + 1, rest.outputCons + 1⟩

@[simp] theorem values_readBatch {A : Type u} {R : Type w}
    (reader : A → ReadResult R) (assignments : List A) :
    (readBatch reader assignments).values = assignments.map (fun a => (reader a).value) := by
  induction assignments <;> simp [readBatch, *]

@[simp] theorem reads_readBatch {A : Type u} {R : Type w}
    (reader : A → ReadResult R) (assignments : List A) :
    (readBatch reader assignments).reads = ReadWork.sum (assignments.map (fun a => (reader a).work)) := by
  induction assignments <;> simp [readBatch, ReadWork.sum, *]

@[simp] theorem cases_readBatch {A : Type u} {R : Type w}
    (reader : A → ReadResult R) (assignments : List A) :
    (readBatch reader assignments).assignmentListCases = assignments.length + 1 := by
  induction assignments <;> simp [readBatch, *, Nat.add_assoc]

@[simp] theorem cons_readBatch {A : Type u} {R : Type w}
    (reader : A → ReadResult R) (assignments : List A) :
    (readBatch reader assignments).outputCons = assignments.length := by
  induction assignments <;> simp [readBatch, *]

namespace CachedTable

variable {α : Type u} {D : Type v} {R : Type w}
variable [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D]

/-- A batch shares one already prepared table; it performs no preprocessing. -/
def readMany (t : CachedTable α D R) (assignments : List (α → D)) : BatchResult R :=
  readBatch t.read assignments

def readManyFin {q : Nat} (t : CachedTable α (Fin q) R)
    (assignments : List (α → Fin q)) : BatchResult R := readBatch t.readFin assignments

theorem values_readMany (t : CachedTable α D R) (assignments : List (α → D)) :
    (t.readMany assignments).values = assignments.map t.table.eval := by
  simp only [readMany, values_readBatch]
  apply List.map_congr_left
  intro a _
  exact t.eval_eq_legacy a

theorem values_readManyFin {q : Nat} (t : CachedTable α (Fin q) R)
    (assignments : List (α → Fin q)) :
    (t.readManyFin assignments).values = assignments.map t.table.eval := by
  simp only [readManyFin, values_readBatch]
  apply List.map_congr_left
  intro a _
  exact (t.evalFin_eq_eval a).trans (t.eval_eq_legacy a)

/-- Exact repeated-read charges in the specialized path, including coordinate
traversals and one array read per assignment, but no colour search. -/
theorem reads_readManyFin {q : Nat} (t : CachedTable α (Fin q) R)
    (assignments : List (α → Fin q)) :
    (t.readManyFin assignments).reads =
      ⟨assignments.length * (Fintype.card α + 1), 0, 0, 0,
        assignments.length * Fintype.card α,
        assignments.length * Fintype.card α, assignments.length⟩ := by
  induction assignments with
  | nil => simp [readManyFin, readBatch, ReadWork.zero]
  | cons a assignments ih =>
      simp only [readManyFin, readBatch] at ih ⊢
      rw [work_readFin, ih]
      simp [ReadWork.add, Nat.add_mul, Nat.add_comm]

end CachedTable

/-- Preparation costs are stored once alongside the work of all subsequent
reads. This result deliberately does not flatten unlike operation categories. -/
structure PreparedBatch (n q : Nat) (R : Type) where
  preparation : FinCachePreparation n q R
  batch : BatchResult R

def prepareReadManyFin {n q : Nat} {R : Type}
    (table : Counting.Algorithm.VariableElimination.DenseTable (Fin n) (Fin q) R)
    (assignments : List (Fin n → Fin q)) : PreparedBatch n q R :=
  let prepared := cacheFinTable table
  ⟨prepared, prepared.cache.readManyFin assignments⟩

@[simp] theorem preparation_prepareReadManyFin {n q : Nat} {R : Type}
    (table : Counting.Algorithm.VariableElimination.DenseTable (Fin n) (Fin q) R)
    (assignments : List (Fin n → Fin q)) :
    (prepareReadManyFin table assignments).preparation = cacheFinTable table := rfl

theorem values_prepareReadManyFin {n q : Nat} {R : Type}
    (table : Counting.Algorithm.VariableElimination.DenseTable (Fin n) (Fin q) R)
    (assignments : List (Fin n → Fin q)) :
    (prepareReadManyFin table assignments).batch.values = assignments.map table.eval := by
  exact CachedTable.values_readManyFin _ _

theorem reads_prepareReadManyFin {n q : Nat} {R : Type}
    (table : Counting.Algorithm.VariableElimination.DenseTable (Fin n) (Fin q) R)
    (assignments : List (Fin n → Fin q)) :
    (prepareReadManyFin table assignments).batch.reads =
      ⟨assignments.length * (n + 1), 0, 0, 0,
        assignments.length * n, assignments.length * n, assignments.length⟩ := by
  simpa only [prepareReadManyFin, Fintype.card_fin] using
    CachedTable.reads_readManyFin (cacheFinTable table).cache assignments

end Counting.Algorithm.VariableEliminationLayout
