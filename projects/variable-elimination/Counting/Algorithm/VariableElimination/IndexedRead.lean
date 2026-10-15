import Counting.Algorithm.VariableElimination.Table
import Counting.Algorithm.VariableElimination.AddressCost

/-!
# Instrumented direct table reads

A read records address arithmetic, colour comparisons, one array access, and the
sizes of the coordinate/colour enumerations prepared for the address. Enumeration
sizes are resource counts, not claims about sorting or allocation running time.
They make the per-read preprocessing explicit; no bit-time bound is claimed.
-/

namespace Counting.Algorithm.VariableElimination

universe u v w

/-- Resource observations for one table read. The returned coefficient is kept
separate from address arithmetic and no coefficient operation is performed. -/
structure IndexedReadMeasured (R : Type w) where
  value : R
  address : AddressMeasured
  arrayReads : Nat
  coordinateEntries : Nat
  colourEntries : Nat

namespace DenseTable

variable {α : Type u} {D : Type v} {R : Type w}
variable [Fintype α] [LinearOrder α]

/-- Execute measured Horner addressing and one array read. The enumerated lists
are shared by the fold and their recorded preprocessing sizes. -/
def evalIndexedMeasured [Fintype D] [LinearOrder D]
    (t : DenseTable α D R) (a : α → D) : IndexedReadMeasured R :=
  let xs := enumerateValues α
  let ds := enumerateValues D
  let address := measuredHorner ds.length (fun x => measuredIdxOf (a x) ds) xs
  let value := t.values[address.value]'(by
    rw [t.size_values]
    change (measuredAssignmentIndex a).value < _
    rw [value_measuredAssignmentIndex]
    exact assignmentIndex_lt a)
  ⟨value, address, 1, xs.length, ds.length⟩

@[simp] theorem value_evalIndexedMeasured [Fintype D] [LinearOrder D]
    (t : DenseTable α D R) (a : α → D) :
    (t.evalIndexedMeasured a).value = t.evalIndexed a := by
  have h : (measuredAssignmentIndex a).value < t.values.size := by
    rw [t.size_values, value_measuredAssignmentIndex]
    exact assignmentIndex_lt a
  change t.values[(measuredAssignmentIndex a).value]'h = _
  simp only [value_measuredAssignmentIndex, evalIndexed]

@[simp] theorem address_evalIndexedMeasured [Fintype D] [LinearOrder D]
    (t : DenseTable α D R) (a : α → D) :
    (t.evalIndexedMeasured a).address = measuredAssignmentIndex a := rfl

@[simp] theorem arrayReads_evalIndexedMeasured [Fintype D] [LinearOrder D]
    (t : DenseTable α D R) (a : α → D) :
    (t.evalIndexedMeasured a).arrayReads = 1 := rfl

@[simp] theorem coordinateEntries_evalIndexedMeasured [Fintype D] [LinearOrder D]
    (t : DenseTable α D R) (a : α → D) :
    (t.evalIndexedMeasured a).coordinateEntries = Fintype.card α := by
  simp [evalIndexedMeasured]

@[simp] theorem colourEntries_evalIndexedMeasured [Fintype D] [LinearOrder D]
    (t : DenseTable α D R) (a : α → D) :
    (t.evalIndexedMeasured a).colourEntries = Fintype.card D := by
  simp [evalIndexedMeasured]

/-- Finite-ordinal colours require no colour enumeration or search. This path
prepares the coordinate list, performs its Horner fold, and reads one array entry. -/
def evalFinIndexedMeasured {q : Nat} (t : DenseTable α (Fin q) R)
    (a : α → Fin q) : IndexedReadMeasured R :=
  let xs := enumerateValues α
  let address := measuredHorner q (fun x => ⟨(a x).val, 0⟩) xs
  let value := t.values[address.value]'(by
    rw [t.size_values, Fintype.card_fin]
    change (measuredAssignmentIndexFin q a).value < _
    rw [value_measuredAssignmentIndexFin]
    exact assignmentIndexFin_lt q a)
  ⟨value, address, 1, xs.length, 0⟩

@[simp] theorem value_evalFinIndexedMeasured {q : Nat} (t : DenseTable α (Fin q) R)
    (a : α → Fin q) : (t.evalFinIndexedMeasured a).value = t.evalFinIndexed a := by
  have h : (measuredAssignmentIndexFin q a).value < t.values.size := by
    rw [t.size_values, Fintype.card_fin, value_measuredAssignmentIndexFin]
    exact assignmentIndexFin_lt q a
  change t.values[(measuredAssignmentIndexFin q a).value]'h = _
  simp only [value_measuredAssignmentIndexFin, evalFinIndexed]

@[simp] theorem address_evalFinIndexedMeasured {q : Nat}
    (t : DenseTable α (Fin q) R) (a : α → Fin q) :
    (t.evalFinIndexedMeasured a).address = measuredAssignmentIndexFin q a := rfl

@[simp] theorem arrayReads_evalFinIndexedMeasured {q : Nat}
    (t : DenseTable α (Fin q) R) (a : α → Fin q) :
    (t.evalFinIndexedMeasured a).arrayReads = 1 := rfl

@[simp] theorem coordinateEntries_evalFinIndexedMeasured {q : Nat}
    (t : DenseTable α (Fin q) R) (a : α → Fin q) :
    (t.evalFinIndexedMeasured a).coordinateEntries = Fintype.card α := by
  simp [evalFinIndexedMeasured]

@[simp] theorem colourEntries_evalFinIndexedMeasured {q : Nat}
    (t : DenseTable α (Fin q) R) (a : α → Fin q) :
    (t.evalFinIndexedMeasured a).colourEntries = 0 := rfl

end DenseTable

end Counting.Algorithm.VariableElimination
