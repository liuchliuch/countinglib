import Counting.Algorithm.VariableElimination.IndexedRead
import Counting.Algorithm.VariableElimination.Model
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum

/-!
# Direct-address regression clients

The declarations below are kernel checked. The final executable assertions also
exercise both direct table-read paths and the measured address computations.
The stored arrays are supplied directly, independently of `DenseTable.tabulate`.
-/

namespace Counting.Algorithm.VariableElimination.IndexedExamples

/-- Two ports, with the first port occupying the most significant position. -/
def pairAssignment (x y : Fin 2) : Fin 2 → Fin 2 :=
  fun i => if i = 0 then x else y

def twoBitInputs : List (Fin 2 → Fin 2) :=
  [pairAssignment 0 0, pairAssignment 0 1, pairAssignment 1 0, pairAssignment 1 1]

def fourRows : DenseTable (Fin 2) (Fin 2) Nat :=
  ⟨#[11, 13, 17, 19], by decide⟩

theorem fin_addresses : twoBitInputs.map (assignmentIndexFin 2) = [0, 1, 2, 3] := by
  simp only [twoBitInputs, List.map_cons, List.map_nil, assignmentIndexFin,
    hornerIndex, enumerateValues_fin]
  decide

theorem general_addresses : twoBitInputs.map assignmentIndex = [0, 1, 2, 3] := by
  have h : assignmentIndexFin 2 = (assignmentIndex : (Fin 2 → Fin 2) → Nat) :=
    funext (assignmentIndexFin_eq_assignmentIndex 2)
  rw [← h]
  exact fin_addresses

theorem fin_reads : twoBitInputs.map fourRows.evalFinIndexed = [11, 13, 17, 19] := by
  simp only [twoBitInputs, List.map_cons, List.map_nil, DenseTable.evalFinIndexed,
    assignmentIndexFin, hornerIndex, enumerateValues_fin, fourRows]
  decide

theorem general_reads : twoBitInputs.map fourRows.evalIndexed = [11, 13, 17, 19] := by
  have h : fourRows.evalFinIndexed = fourRows.evalIndexed :=
    funext (DenseTable.evalFinIndexed_eq_evalIndexed fourRows)
  rw [← h]
  exact fin_reads

/-- Compatibility covers an arbitrary preexisting array, without assuming it
was produced by tabulation. -/
theorem arbitrary_array_compatible (t : DenseTable (Fin 2) (Fin 2) ℚ)
    (a : Fin 2 → Fin 2) : t.evalFinIndexed a = t.eval a := by
  rw [DenseTable.evalFinIndexed_eq_evalIndexed, DenseTable.evalIndexed_eq_eval]

def boolRows : DenseTable Bool Bool Nat := ⟨#[23, 29, 31, 37], by decide⟩

private theorem enumerateValues_bool : enumerateValues Bool = [false, true] := by
  have hs : ([false, true] : List Bool).toFinset = Finset.univ := by decide
  rw [enumerateValues, ← hs]
  exact (List.toFinset_sort (· ≤ ·) (by decide)).mpr (by decide)

theorem bool_address : assignmentIndex (fun b : Bool => !b) = 2 := by
  simp only [assignmentIndex, hornerIndex, enumerateValues_bool]
  decide

theorem bool_read : boolRows.evalIndexed (fun b : Bool => !b) = 31 := by
  simp [DenseTable.evalIndexed, bool_address, boolRows]

def rationalRows : DenseTable (Fin 2) (Fin 2) ℚ :=
  ⟨#[1 / 2, 2 / 3, 3 / 4, 5 / 6], by decide⟩

theorem rational_read : rationalRows.evalFinIndexed (pairAssignment 1 0) = 3 / 4 := by
  simp only [DenseTable.evalFinIndexed, assignmentIndexFin, hornerIndex,
    enumerateValues_fin, rationalRows]
  rfl

def emptyDomainRows : DenseTable (Fin 1) (Fin 0) Nat := ⟨#[], by decide⟩

theorem empty_domain_has_no_assignment (a : Fin 1 → Fin 0) : False := Fin.elim0 (a 0)

theorem empty_domain_has_no_rows : emptyDomainRows.rowCount = 0 := by decide

/-- Zero coordinates still have one assignment even when the domain is empty. -/
def emptyCoordinateRows : DenseTable (Fin 0) (Fin 0) Nat := ⟨#[7], by decide⟩

theorem empty_address : assignmentIndex (Fin.elim0 : Fin 0 → Fin 0) = 0 := by
  simp [assignmentIndex, hornerIndex]

theorem empty_fin_address : assignmentIndexFin 0 (Fin.elim0 : Fin 0 → Fin 0) = 0 := by
  simp [assignmentIndexFin, hornerIndex]

theorem empty_coordinate_read :
    emptyCoordinateRows.evalIndexed (Fin.elim0 : Fin 0 → Fin 0) = 7 := by
  simp [DenseTable.evalIndexed, empty_address, emptyCoordinateRows]

theorem empty_coordinate_fin_read :
    emptyCoordinateRows.evalFinIndexed (Fin.elim0 : Fin 0 → Fin 0) = 7 := by
  rw [DenseTable.evalFinIndexed_eq_evalIndexed, empty_coordinate_read]

def singletonDomainRows : DenseTable (Fin 3) (Fin 1) Nat := ⟨#[41], by decide⟩

theorem singleton_address : assignmentIndexFin 1 (fun _ : Fin 3 => (0 : Fin 1)) = 0 := by
  simp only [assignmentIndexFin, hornerIndex, enumerateValues_fin]
  decide

theorem singleton_read :
    singletonDomainRows.evalFinIndexed (fun _ : Fin 3 => (0 : Fin 1)) = 41 := by
  simp [DenseTable.evalFinIndexed, singleton_address, singletonDomainRows]

/-- Both ordered ports refer to one global variable; the stored table still has
two coordinates and four rows. -/
def repeatedPortFactor : Factor (Fin 1) (Fin 2) Nat :=
  ⟨2, fun _ => 0, fourRows.evalIndexed⟩

theorem repeated_ports_address :
    assignmentIndexFin 2 ((fun _ : Fin 1 => (1 : Fin 2)) ∘ repeatedPortFactor.scope) = 3 := by
  change assignmentIndexFin 2 (fun _ : Fin 2 => 1) = 3
  simp only [assignmentIndexFin, hornerIndex, enumerateValues_fin]
  decide

theorem repeated_ports_read : repeatedPortFactor.eval (fun _ => 1) = 19 := by
  change fourRows.evalIndexed (fun _ : Fin 2 => 1) = 19
  rw [← DenseTable.evalFinIndexed_eq_evalIndexed]
  have h : assignmentIndexFin 2 (fun _ : Fin 2 => 1) = 3 := repeated_ports_address
  simp [DenseTable.evalFinIndexed, h, fourRows]

theorem repeated_ports_rows : fourRows.rowCount = 4 := by decide

/-- Counter summaries retain the distinction between Horner arithmetic and
colour equality tests. Coefficient operations have no fields in this record. -/
def addressCounts (r : AddressMeasured) : Nat × Nat × Nat :=
  (r.hornerAdditions, r.hornerMultiplications, r.colourComparisons)

theorem generic_address_counts :
    addressCounts (measuredAssignmentIndex (pairAssignment 1 0)) = (2, 2, 3) := by
  simp only [addressCounts, additions_measuredAssignmentIndex,
    multiplications_measuredAssignmentIndex, Fintype.card_fin,
    comparisons_measuredAssignmentIndex, enumerateValues_fin]
  decide

theorem fin_address_counts :
    addressCounts (measuredAssignmentIndexFin 2 (pairAssignment 1 0)) = (2, 2, 0) := by
  simp [addressCounts]

theorem empty_address_counts :
    addressCounts (measuredAssignmentIndex (Fin.elim0 : Fin 0 → Fin 0)) = (0, 0, 0) := by
  simp [addressCounts, comparisons_measuredAssignmentIndex]

theorem singleton_address_counts :
    addressCounts (measuredAssignmentIndex (fun _ : Fin 3 => (0 : Fin 1))) = (3, 3, 3) := by
  simp only [addressCounts, additions_measuredAssignmentIndex,
    multiplications_measuredAssignmentIndex, Fintype.card_fin,
    comparisons_measuredAssignmentIndex, enumerateValues_fin]
  decide

theorem duplicate_colour_search :
    measuredIdxOf (1 : Fin 2) [0, 1, 1] = ⟨1, 2⟩ := rfl

theorem absent_colour_search :
    measuredIdxOf (1 : Fin 2) [0, 0] = ⟨2, 2⟩ := rfl

/-- Enumeration entries are resource sizes; they do not measure sorting or
allocation time. The array-read field records the one actual stored lookup. -/
def readCounts {R : Type} (r : IndexedReadMeasured R) :
    (Nat × Nat × Nat) × Nat × Nat × Nat :=
  (addressCounts r.address, r.arrayReads, r.coordinateEntries, r.colourEntries)

theorem generic_table_read_counts :
    readCounts (fourRows.evalIndexedMeasured (pairAssignment 1 0)) =
      ((2, 2, 3), 1, 2, 2) := by
  simp [readCounts, generic_address_counts]

theorem fin_table_read_counts :
    readCounts (fourRows.evalFinIndexedMeasured (pairAssignment 1 0)) =
      ((2, 2, 0), 1, 2, 0) := by
  simp [readCounts, fin_address_counts]

theorem empty_table_read_counts :
    readCounts (emptyCoordinateRows.evalIndexedMeasured (Fin.elim0 : Fin 0 → Fin 0)) =
      ((0, 0, 0), 1, 0, 0) := by
  simp [readCounts, empty_address_counts]

theorem singleton_table_read_counts :
    readCounts (singletonDomainRows.evalIndexedMeasured (fun _ => 0)) =
      ((3, 3, 3), 1, 3, 1) := by
  simp [readCounts, singleton_address_counts]

theorem rational_measured_read :
    (rationalRows.evalFinIndexedMeasured (pairAssignment 1 0)).value = 3 / 4 := by
  simp [rational_read]

#eval do
  unless twoBitInputs.map (assignmentIndexFin 2) == [0, 1, 2, 3] do
    throw (IO.userError "Fin direct addresses changed")
  unless twoBitInputs.map assignmentIndex == [0, 1, 2, 3] do
    throw (IO.userError "Generic direct addresses changed")
  unless twoBitInputs.map fourRows.evalIndexed == [11, 13, 17, 19] do
    throw (IO.userError "Generic direct reads changed")
  unless twoBitInputs.map fourRows.evalFinIndexed == [11, 13, 17, 19] do
    throw (IO.userError "Fin direct reads changed")
  unless boolRows.evalIndexed (fun b => !b) == 31 do
    throw (IO.userError "Boolean ordered-domain read changed")
  unless rationalRows.evalFinIndexed (pairAssignment 1 0) == (3 / 4 : ℚ) do
    throw (IO.userError "Rational direct read changed")
  unless emptyCoordinateRows.evalFinIndexed (Fin.elim0 : Fin 0 → Fin 0) == 7 do
    throw (IO.userError "Empty-coordinate empty-domain read changed")
  unless singletonDomainRows.evalFinIndexed (fun _ => 0) == 41 do
    throw (IO.userError "Singleton-domain direct read changed")
  unless repeatedPortFactor.eval (fun _ => 1) == 19 do
    throw (IO.userError "Repeated-port direct read changed")
  unless addressCounts (measuredAssignmentIndex (pairAssignment 1 0)) == (2, 2, 3) do
    throw (IO.userError "Generic measured address counts changed")
  unless addressCounts (measuredAssignmentIndexFin 2 (pairAssignment 1 0)) == (2, 2, 0) do
    throw (IO.userError "Fin measured address counts changed")
  unless addressCounts (measuredAssignmentIndex (Fin.elim0 : Fin 0 → Fin 0)) == (0, 0, 0) do
    throw (IO.userError "Empty-address counts changed")
  let genericRead := fourRows.evalIndexedMeasured (pairAssignment 1 0)
  unless genericRead.value == 17 && readCounts genericRead == ((2, 2, 3), 1, 2, 2) do
    throw (IO.userError "Generic measured table read changed")
  let finRead := fourRows.evalFinIndexedMeasured (pairAssignment 1 0)
  unless finRead.value == 17 && readCounts finRead == ((2, 2, 0), 1, 2, 0) do
    throw (IO.userError "Fin measured table read changed")
  let emptyRead := emptyCoordinateRows.evalIndexedMeasured (Fin.elim0 : Fin 0 → Fin 0)
  unless emptyRead.value == 7 && readCounts emptyRead == ((0, 0, 0), 1, 0, 0) do
    throw (IO.userError "Empty measured table read changed")
  let rationalRead := rationalRows.evalFinIndexedMeasured (pairAssignment 1 0)
  unless rationalRead.value == (3 / 4 : ℚ) do
    throw (IO.userError "Rational measured table read changed")
  IO.println "All direct-address executable regression assertions passed."

end Counting.Algorithm.VariableElimination.IndexedExamples
