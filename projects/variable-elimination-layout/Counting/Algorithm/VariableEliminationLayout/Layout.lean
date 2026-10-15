import Counting.Algorithm.VariableEliminationLayout.Sort
import Counting.Algorithm.VariableElimination.Index

/-! # Prepared, reusable table layouts -/

namespace Counting.Algorithm.VariableEliminationLayout

universe u v

open Counting.Algorithm.VariableElimination

/-- Actual traversal for caching a list's length. Counter arithmetic is excluded
from the data-program operation model. -/
structure LengthResult where
  value : Nat
  listCases : Nat
  increments : Nat
  deriving Repr

def lengthCounted {α : Type u} : List α → LengthResult
  | [] => ⟨0, 1, 0⟩
  | _ :: xs =>
      let t := lengthCounted xs
      ⟨t.value + 1, t.listCases + 1, t.increments + 1⟩

@[simp] theorem value_lengthCounted {α : Type u} (xs : List α) :
    (lengthCounted xs).value = xs.length := by
  induction xs <;> simp [lengthCounted, *]

@[simp] theorem cases_lengthCounted {α : Type u} (xs : List α) :
    (lengthCounted xs).listCases = xs.length + 1 := by
  induction xs <;> simp [lengthCounted, *, Nat.add_assoc]

@[simp] theorem increments_lengthCounted {α : Type u} (xs : List α) :
    (lengthCounted xs).increments = xs.length := by
  induction xs <;> simp [lengthCounted, *]

/-- Cached coordinate and colour lists, with a cached radix. Their invariants
specify the established table layout; the preparation program constructs them. -/
structure TableLayout (α : Type u) (D : Type v)
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D] where
  coordinates : List α
  colours : List D
  radix : Nat
  coordinates_eq : coordinates = enumerateValues α
  colours_eq : colours = enumerateValues D
  radix_eq : radix = colours.length

/-- Preparation retains separate sort and length-traversal observations. The
input enumeration lists themselves are explicit input data. -/
structure LayoutPreparation (α : Type u) (D : Type v)
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D] where
  layout : TableLayout α D
  coordinateSort : SortWork
  colourSort : SortWork
  radixTraversal : LengthResult
  layoutConstructions : Nat

/-- Prepare once: actually sort each supplied enumeration and traverse the
prepared colour list once to cache its radix. -/
def prepareLayout {α : Type u} {D : Type v}
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D]
    (coordinates : EnumerationSource α) (colours : EnumerationSource D) :
    LayoutPreparation α D :=
  let xs := sortCounted coordinates.values
  let ds := sortCounted colours.values
  let q := lengthCounted ds.values
  ⟨⟨xs.values, ds.values, q.value, coordinates.prepared_eq_enumerateValues,
      colours.prepared_eq_enumerateValues, value_lengthCounted _⟩,
    xs.work, ds.work, q, 1⟩

@[simp] theorem coordinateSort_prepareLayout {α : Type u} {D : Type v}
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D]
    (xs : EnumerationSource α) (ds : EnumerationSource D) :
    (prepareLayout xs ds).coordinateSort = (sortCounted xs.values).work := rfl

@[simp] theorem colourSort_prepareLayout {α : Type u} {D : Type v}
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D]
    (xs : EnumerationSource α) (ds : EnumerationSource D) :
    (prepareLayout xs ds).colourSort = (sortCounted ds.values).work := rfl

@[simp] theorem radixTraversal_prepareLayout {α : Type u} {D : Type v}
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D]
    (xs : EnumerationSource α) (ds : EnumerationSource D) :
    (prepareLayout xs ds).radixTraversal =
      lengthCounted (sortCounted ds.values).values := rfl

@[simp] theorem constructions_prepareLayout {α : Type u} {D : Type v}
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D]
    (xs : EnumerationSource α) (ds : EnumerationSource D) :
    (prepareLayout xs ds).layoutConstructions = 1 := rfl

namespace TableLayout

variable {α : Type u} {D : Type v}
variable [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D]

@[simp] theorem length_coordinates (l : TableLayout α D) :
    l.coordinates.length = Fintype.card α := by rw [l.coordinates_eq]; simp

@[simp] theorem length_colours (l : TableLayout α D) :
    l.colours.length = Fintype.card D := by rw [l.colours_eq]; simp

@[simp] theorem radix_eq_card (l : TableLayout α D) : l.radix = Fintype.card D := by
  rw [l.radix_eq, length_colours]

/-- The cached reader traverses stored lists only. It does not call a sorting,
enumeration, or assignment-generation routine. -/
def index (l : TableLayout α D) (a : α → D) : Nat :=
  hornerIndex l.radix (fun x => l.colours.idxOf (a x)) l.coordinates

theorem index_eq_assignmentIndex (l : TableLayout α D) (a : α → D) :
    l.index a = assignmentIndex a := by
  simp [index, assignmentIndex, l.coordinates_eq, l.colours_eq]

theorem index_lt (l : TableLayout α D) (a : α → D) :
    l.index a < Fintype.card D ^ Fintype.card α := by
  rw [index_eq_assignmentIndex]
  exact assignmentIndex_lt a

/-- Specialized cached address. Fin digits are read directly; the colour list
is not accessed, and even coordinate enumeration is already cached. -/
def indexFin {q : Nat} (l : TableLayout α (Fin q)) (a : α → Fin q) : Nat :=
  hornerIndex q (fun x => (a x).val) l.coordinates

theorem indexFin_eq_index {q : Nat} (l : TableLayout α (Fin q)) (a : α → Fin q) :
    l.indexFin a = l.index a := by
  rw [index_eq_assignmentIndex]
  simpa [indexFin, assignmentIndexFin, l.coordinates_eq] using
    assignmentIndexFin_eq_assignmentIndex q a

end TableLayout

end Counting.Algorithm.VariableEliminationLayout
