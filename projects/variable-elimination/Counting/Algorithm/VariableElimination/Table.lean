import Counting.Algorithm.VariableElimination.Index

namespace Counting.Algorithm.VariableElimination

universe u v w

/-- A dense finite table stores one array entry for every assignment. -/
structure DenseTable (α : Type u) (D : Type v) (R : Type w)
    [Fintype α] [Fintype D] where
  values : Array R
  size_values : values.size = Fintype.card D ^ Fintype.card α

namespace DenseTable

variable {α : Type u} {D : Type v} {R : Type w}
variable [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D]

/-- Construct the array by evaluating the function at every assignment. -/
def tabulate (f : (α → D) → R) : DenseTable α D R where
  values := ((enumerateAssignments α D).map f).toArray
  size_values := by simp

/-- The number of stored values, including the unique empty assignment. -/
def rowCount (t : DenseTable α D R) : Nat := t.values.size

omit [LinearOrder α] [LinearOrder D] in
@[simp] theorem rowCount_eq (t : DenseTable α D R) :
    t.rowCount = Fintype.card D ^ Fintype.card α := t.size_values

/-- Read the stored entry at the canonical index of an assignment. This executable
lookup uses a linear search of the assignment list. -/
def eval (t : DenseTable α D R) (a : α → D) : R :=
  t.values[(enumerateAssignments α D).idxOf a]'(by
    rw [t.size_values, ← length_enumerateAssignments α D]
    exact List.idxOf_lt_length_of_mem (mem_enumerateAssignments a))

@[simp] theorem eval_tabulate (f : (α → D) → R) (a : α → D) :
    (tabulate f).eval a = f a := by
  simp [eval, tabulate, List.getElem_idxOf]


/-- Read a table with a Horner address. This path enumerates coordinates and
colours, but never enumerates the assignment space. -/
def evalIndexed (t : DenseTable α D R) (a : α → D) : R :=
  t.values[assignmentIndex a]'(by rw [t.size_values]; exact assignmentIndex_lt a)

/-- Every old table has the same interpretation under the direct address. The
statement applies to arbitrary arrays satisfying the table-size invariant. -/
theorem evalIndexed_eq_eval (t : DenseTable α D R) (a : α → D) :
    t.evalIndexed a = t.eval a := by
  simp only [evalIndexed, eval, idxOf_enumerateAssignments_eq_assignmentIndex]

@[simp] theorem evalIndexed_tabulate (f : (α → D) → R) (a : α → D) :
    (tabulate f).evalIndexed a = f a := by
  rw [evalIndexed_eq_eval, eval_tabulate]

/-- Direct addresses for Fin colours read the same array without colour search. -/
def evalFinIndexed {q : Nat} (t : DenseTable α (Fin q) R) (a : α → Fin q) : R :=
  t.values[assignmentIndexFin q a]'(by
    rw [t.size_values, Fintype.card_fin]
    exact assignmentIndexFin_lt q a)

theorem evalFinIndexed_eq_evalIndexed {q : Nat}
    (t : DenseTable α (Fin q) R) (a : α → Fin q) :
    t.evalFinIndexed a = t.evalIndexed a := by
  simp only [evalFinIndexed, evalIndexed, assignmentIndexFin_eq_assignmentIndex]

@[simp] theorem evalFinIndexed_tabulate {q : Nat} (f : (α → Fin q) → R)
    (a : α → Fin q) : (tabulate f).evalFinIndexed a = f a := by
  rw [evalFinIndexed_eq_evalIndexed, evalIndexed_tabulate]

@[simp] theorem values_tabulate (f : (α → D) → R) :
    (tabulate f).values = ((enumerateAssignments α D).map f).toArray := rfl

/-- The enumeration and the materialized array have the same size. -/
theorem length_enumeration_eq_rowCount (f : (α → D) → R) :
    (enumerateAssignments α D).length = (tabulate f).rowCount := by simp

end DenseTable

end Counting.Algorithm.VariableElimination
