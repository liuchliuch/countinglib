import Counting.Algorithm.VariableElimination.Index

/-!
# Address-operation instrumentation

These counters are separate from coefficient arithmetic in `Measured`. A Horner
step performs one natural-number multiplication and one natural-number addition.
Colour lookup counts equality comparisons. Enumeration, search-index increments,
counter bookkeeping, allocation, and bit costs are outside these counters.
-/

namespace Counting.Algorithm.VariableElimination

universe u v

/-- The result of a colour search and the equality comparisons it performed. -/
structure ColourLookup where
  value : Nat
  comparisons : Nat
  deriving Repr

/-- Linear search, stopping at the first matching colour. Absence returns the
list length, as `List.idxOf` does. -/
def measuredIdxOf {D : Type v} [DecidableEq D] (d : D) : List D → ColourLookup
  | [] => ⟨0, 0⟩
  | c :: cs =>
      if c = d then ⟨0, 1⟩
      else
        let tail := measuredIdxOf d cs
        ⟨tail.value + 1, tail.comparisons + 1⟩

@[simp] theorem value_measuredIdxOf {D : Type v} [DecidableEq D]
    (d : D) (ds : List D) : (measuredIdxOf d ds).value = ds.idxOf d := by
  induction ds with
  | nil => simp [measuredIdxOf]
  | cons c cs ih =>
      by_cases h : c = d
      · subst c; simp [measuredIdxOf]
      · simp [measuredIdxOf, h, ih, List.idxOf_cons_ne cs h]

/-- A successful search performs one comparison for each preceding colour and
one for the matching colour. This does not require a duplicate-free list. -/
theorem comparisons_measuredIdxOf_of_mem {D : Type v} [DecidableEq D]
    (d : D) (ds : List D) (hd : d ∈ ds) :
    (measuredIdxOf d ds).comparisons = ds.idxOf d + 1 := by
  induction ds with
  | nil => simp at hd
  | cons c cs ih =>
      by_cases h : c = d
      · subst c; simp [measuredIdxOf]
      · have ht : d ∈ cs := by simpa [Ne.symm h] using hd
        simp [measuredIdxOf, h, ih ht, List.idxOf_cons_ne cs h]

/-- Search always uses at most one equality comparison per list entry. -/
theorem comparisons_measuredIdxOf_le {D : Type v} [DecidableEq D]
    (d : D) (ds : List D) : (measuredIdxOf d ds).comparisons ≤ ds.length := by
  induction ds with
  | nil => simp [measuredIdxOf]
  | cons c cs ih =>
      by_cases h : c = d
      · simp [measuredIdxOf, h]
      · simpa [measuredIdxOf, h] using Nat.add_le_add_right ih 1

/-- Natural arithmetic in Horner addressing and equality comparisons in colour
lookup. These fields never count coefficient operations. -/
structure AddressMeasured where
  value : Nat
  hornerAdditions : Nat
  hornerMultiplications : Nat
  colourComparisons : Nat
  deriving Repr

/-- One actual Horner multiply-add, using one computed digit. -/
def measuredHornerStep {α : Type u} (q : Nat) (digit : α → ColourLookup)
    (acc : AddressMeasured) (x : α) : AddressMeasured :=
  let d := digit x
  ⟨acc.value * q + d.value, acc.hornerAdditions + 1,
    acc.hornerMultiplications + 1, acc.colourComparisons + d.comparisons⟩

/-- Address computation follows the literal left fold `acc * q + digit x`. -/
def measuredHorner {α : Type u} (q : Nat) (digit : α → ColourLookup)
    (xs : List α) : AddressMeasured :=
  xs.foldl (measuredHornerStep q digit) ⟨0, 0, 0, 0⟩

theorem foldl_measuredHornerStep {α : Type u} (q : Nat)
    (digit : α → ColourLookup) (xs : List α) (acc : AddressMeasured) :
    xs.foldl (measuredHornerStep q digit) acc =
      ⟨xs.foldl (fun n x => n * q + (digit x).value) acc.value,
        acc.hornerAdditions + xs.length, acc.hornerMultiplications + xs.length,
        acc.colourComparisons + (xs.map (fun x => (digit x).comparisons)).sum⟩ := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp [List.foldl_cons, ih, measuredHornerStep, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

@[simp] theorem value_measuredHorner {α : Type u} (q : Nat)
    (digit : α → ColourLookup) (xs : List α) :
    (measuredHorner q digit xs).value =
      xs.foldl (fun n x => n * q + (digit x).value) 0 := by
  simp [measuredHorner, foldl_measuredHornerStep]

theorem value_measuredHorner_eq_hornerIndex {α : Type u} (q : Nat)
    (digit : α → ColourLookup) (xs : List α) :
    (measuredHorner q digit xs).value =
      hornerIndex q (fun x => (digit x).value) xs := by
  simp [hornerIndex]

@[simp] theorem additions_measuredHorner {α : Type u} (q : Nat)
    (digit : α → ColourLookup) (xs : List α) :
    (measuredHorner q digit xs).hornerAdditions = xs.length := by
  simp [measuredHorner, foldl_measuredHornerStep]

@[simp] theorem multiplications_measuredHorner {α : Type u} (q : Nat)
    (digit : α → ColourLookup) (xs : List α) :
    (measuredHorner q digit xs).hornerMultiplications = xs.length := by
  simp [measuredHorner, foldl_measuredHornerStep]

@[simp] theorem comparisons_measuredHorner {α : Type u} (q : Nat)
    (digit : α → ColourLookup) (xs : List α) :
    (measuredHorner q digit xs).colourComparisons =
      (xs.map (fun x => (digit x).comparisons)).sum := by
  simp [measuredHorner, foldl_measuredHornerStep]

theorem comparisons_measuredHorner_le {α : Type u} (q c : Nat)
    (digit : α → ColourLookup) (xs : List α)
    (h : ∀ x ∈ xs, (digit x).comparisons ≤ c) :
    (measuredHorner q digit xs).colourComparisons ≤ xs.length * c := by
  rw [comparisons_measuredHorner]
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega

section Assignment

variable {α : Type u} {D : Type v}
variable [Fintype α] [LinearOrder α]

/-- Compute a row address with measured linear colour searches. The coordinate
and colour enumerations are constructed before the fold; their preprocessing
cost is not included in these counters. -/
def measuredAssignmentIndex [Fintype D] [LinearOrder D] (a : α → D) :
    AddressMeasured :=
  let xs := enumerateValues α
  let ds := enumerateValues D
  measuredHorner ds.length (fun x => measuredIdxOf (a x) ds) xs

theorem value_measuredAssignmentIndex_foldl [Fintype D] [LinearOrder D]
    (a : α → D) :
    (measuredAssignmentIndex a).value = (enumerateValues α).foldl
      (fun n x => n * Fintype.card D + (enumerateValues D).idxOf (a x)) 0 := by
  simp [measuredAssignmentIndex]

@[simp] theorem value_measuredAssignmentIndex [Fintype D] [LinearOrder D]
    (a : α → D) : (measuredAssignmentIndex a).value = assignmentIndex a := by
  simp [measuredAssignmentIndex, assignmentIndex, hornerIndex]

@[simp] theorem additions_measuredAssignmentIndex [Fintype D] [LinearOrder D]
    (a : α → D) :
    (measuredAssignmentIndex a).hornerAdditions = Fintype.card α := by
  simp [measuredAssignmentIndex]

@[simp] theorem multiplications_measuredAssignmentIndex [Fintype D] [LinearOrder D]
    (a : α → D) :
    (measuredAssignmentIndex a).hornerMultiplications = Fintype.card α := by
  simp [measuredAssignmentIndex]

/-- Exact successful-search comparison count over the coordinate list. -/
theorem comparisons_measuredAssignmentIndex [Fintype D] [LinearOrder D]
    (a : α → D) :
    (measuredAssignmentIndex a).colourComparisons =
      ((enumerateValues α).map
        (fun x => (enumerateValues D).idxOf (a x) + 1)).sum := by
  simp [measuredAssignmentIndex, comparisons_measuredIdxOf_of_mem,
    mem_enumerateValues]

/-- At most `n * q` colour comparisons for `n` coordinates and `q` colours. -/
theorem comparisons_measuredAssignmentIndex_le [Fintype D] [LinearOrder D]
    (a : α → D) :
    (measuredAssignmentIndex a).colourComparisons ≤
      Fintype.card α * Fintype.card D := by
  simpa [measuredAssignmentIndex] using
    comparisons_measuredHorner_le (enumerateValues D).length
      (enumerateValues D).length (fun x => measuredIdxOf (a x) (enumerateValues D))
      (enumerateValues α) (fun _ _ => comparisons_measuredIdxOf_le _ _)

/-- Finite ordinals already supply their digits. This executable path reads
`Fin.val` directly, without enumerating or searching the colour domain. -/
def measuredAssignmentIndexFin (q : Nat) (a : α → Fin q) : AddressMeasured :=
  measuredHorner q (fun x => ⟨(a x).val, 0⟩) (enumerateValues α)

theorem value_measuredAssignmentIndexFin_foldl (q : Nat) (a : α → Fin q) :
    (measuredAssignmentIndexFin q a).value = (enumerateValues α).foldl
      (fun n x => n * q + (a x).val) 0 := by
  simp [measuredAssignmentIndexFin]

@[simp] theorem value_measuredAssignmentIndexFin (q : Nat) (a : α → Fin q) :
    (measuredAssignmentIndexFin q a).value = assignmentIndexFin q a := by
  simp [measuredAssignmentIndexFin, assignmentIndexFin, hornerIndex]

@[simp] theorem additions_measuredAssignmentIndexFin (q : Nat) (a : α → Fin q) :
    (measuredAssignmentIndexFin q a).hornerAdditions = Fintype.card α := by
  simp [measuredAssignmentIndexFin]

@[simp] theorem multiplications_measuredAssignmentIndexFin (q : Nat) (a : α → Fin q) :
    (measuredAssignmentIndexFin q a).hornerMultiplications = Fintype.card α := by
  simp [measuredAssignmentIndexFin]

@[simp] theorem comparisons_measuredAssignmentIndexFin (q : Nat) (a : α → Fin q) :
    (measuredAssignmentIndexFin q a).colourComparisons = 0 := by
  simp [measuredAssignmentIndexFin]

end Assignment

end Counting.Algorithm.VariableElimination
