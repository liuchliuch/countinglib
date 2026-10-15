import Counting.Algorithm.VariableEliminationLayout.FinRange
import Counting.Algorithm.VariableElimination.Index

/-!
# Counted construction of complete finite-ordinal assignment lists

The program generates coordinate and colour lists once, recursively builds their
dependent Cartesian product, and constructs the total assignment functions. The
first coordinate is most significant, exactly as in the established dense-table
enumeration. Prefixing, concatenation, and membership erasure are explicit counted
recursions; no unobserved `map`, `flatMap`, or `append` constructs the output.

The observations count logical source operations, not physical heap allocation
or bit time. `assignmentClosures` counts newly constructed prefix and totalization
functions. The empty dependent assignment is the existing `List.Pi.nil` constant.
Administrative currying/control closures, observation bookkeeping, and erased
proofs are excluded. Applying a generated assignment later has its own work,
including the tests inside `List.Pi.cons`; it is not charged during construction.
-/

namespace Counting.Algorithm.VariableEliminationWork

universe u v

open Counting.Algorithm.VariableElimination
open Counting.Algorithm.VariableEliminationLayout

/-- Primitive observations of assignment construction, before array materialization. -/
@[ext] structure AssignmentWork where
  listCases : Nat := 0
  listCons : Nat := 0
  assignmentClosures : Nat := 0
  rangeTests : Nat := 0
  natIncrements : Nat := 0
  nilResults : Nat := 0
  deriving DecidableEq, Repr

namespace AssignmentWork

def add (a b : AssignmentWork) : AssignmentWork :=
  ⟨a.listCases + b.listCases, a.listCons + b.listCons,
    a.assignmentClosures + b.assignmentClosures, a.rangeTests + b.rangeTests,
    a.natIncrements + b.natIncrements, a.nilResults + b.nilResults⟩

/-- Charge a nonempty input-list case and its explicit new data constructors. -/
def step (w : AssignmentWork) (cons closures : Nat) : AssignmentWork :=
  ⟨w.listCases + 1, w.listCons + cons, w.assignmentClosures + closures,
    w.rangeTests, w.natIncrements, w.nilResults⟩

/-- Retain every field of an actual finite-range generation observation. -/
def ofRange (w : FinRangeCost) : AssignmentWork :=
  ⟨w.listTraversals, w.listCons, 0, w.loopTests, w.natIncrements, w.nilResults⟩

theorem add_assoc (a b c : AssignmentWork) : (a.add b).add c = a.add (b.add c) := by
  cases a; cases b; cases c
  simp [add, Nat.add_assoc]

end AssignmentWork

/-- A list and observations accumulated while constructing it. -/
structure AssignmentListResult (A : Type u) where
  values : List A
  work : AssignmentWork

/-- Complete finite assignments, in their established table order. -/
structure AssignmentResult (n q : Nat) where
  values : List (Fin n → Fin q)
  work : AssignmentWork

/-- Work of explicitly copying a prefix into an already constructed suffix. -/
def appendAssignmentWork (rows : Nat) : AssignmentWork :=
  ⟨rows + 1, rows, 0, 0, 0, 0⟩

/-- Work of one traversal constructing one new assignment function per input row. -/
def mapAssignmentWork (rows : Nat) : AssignmentWork :=
  ⟨rows + 1, rows, rows, 0, 0, 1⟩

/-- Work of the colour loop, including prefix construction and explicit copying. -/
def colourAssignmentWork (q rows : Nat) : AssignmentWork :=
  ⟨q * (2 * rows + 3) + 1, 2 * q * rows, q * rows, 0, 0, q + 1⟩

/-- Exact recurrence for the dependent Cartesian-product constructor. -/
def piAssignmentWork : Nat → Nat → AssignmentWork
  | 0, _ => ⟨1, 1, 0, 0, 0, 1⟩
  | n + 1, q =>
      ((piAssignmentWork n q).add (colourAssignmentWork q (q ^ n))).step 0 0

/-- Both finite ranges are generated, with their own tests, increments, and nils. -/
def rangeAssignmentWork (n q : Nat) : AssignmentWork :=
  ⟨0, n + q, 0, n + q + 2, n + q, 2⟩

/-- Exact complete cost: two ranges, dependent assignments, and totalization. -/
def assignmentEnumerationWork (n q : Nat) : AssignmentWork :=
  (rangeAssignmentWork n q).add
    ((piAssignmentWork n q).add (mapAssignmentWork (q ^ n)))

namespace AssignmentEnumeration

/-- Copy the first list recursively, sharing the second list unchanged. -/
def appendCounted {A : Type u} : List A → List A → AssignmentListResult A
  | [], ys => ⟨ys, {listCases := 1}⟩
  | x :: xs, ys =>
      let tail := appendCounted xs ys
      ⟨x :: tail.values, tail.work.step 1 0⟩

@[simp] theorem values_appendCounted {A : Type u} (xs ys : List A) :
    (appendCounted xs ys).values = xs ++ ys := by
  induction xs <;> simp [appendCounted, *]

@[simp] theorem work_appendCounted {A : Type u} (xs ys : List A) :
    (appendCounted xs ys).work = appendAssignmentWork xs.length := by
  induction xs <;> simp [appendCounted, *, appendAssignmentWork, AssignmentWork.step]

/-- Add one fixed head colour to every tail, constructing each prefix closure once. -/
def prefixCounted {A : Type u} {D : Type v} [DecidableEq A]
    (x : A) (xs : List A) (d : D) :
    List (∀ i, i ∈ xs → D) → AssignmentListResult (∀ i, i ∈ x :: xs → D)
  | [] => ⟨[], {listCases := 1, nilResults := 1}⟩
  | f :: fs =>
      let tail := prefixCounted x xs d fs
      ⟨List.Pi.cons x xs d f :: tail.values, tail.work.step 1 1⟩

@[simp] theorem values_prefixCounted {A : Type u} {D : Type v} [DecidableEq A]
    (x : A) (xs : List A) (d : D) (fs : List (∀ i, i ∈ xs → D)) :
    (prefixCounted x xs d fs).values = fs.map (List.Pi.cons x xs d) := by
  induction fs <;> simp [prefixCounted, *]

@[simp] theorem work_prefixCounted {A : Type u} {D : Type v} [DecidableEq A]
    (x : A) (xs : List A) (d : D) (fs : List (∀ i, i ∈ xs → D)) :
    (prefixCounted x xs d fs).work = mapAssignmentWork fs.length := by
  induction fs <;> simp [prefixCounted, *, mapAssignmentWork, AssignmentWork.step]

/-- Emit colour-major blocks, charging both construction and append copying. -/
def coloursCounted {A : Type u} {D : Type v} [DecidableEq A]
    (x : A) (xs : List A) (tails : List (∀ i, i ∈ xs → D)) :
    List D → AssignmentListResult (∀ i, i ∈ x :: xs → D)
  | [] => ⟨[], {listCases := 1, nilResults := 1}⟩
  | d :: ds =>
      let first := prefixCounted x xs d tails
      let rest := coloursCounted x xs tails ds
      let joined := appendCounted first.values rest.values
      ⟨joined.values, (first.work.add (rest.work.add joined.work)).step 0 0⟩

@[simp] theorem values_coloursCounted {A : Type u} {D : Type v} [DecidableEq A]
    (x : A) (xs : List A) (tails : List (∀ i, i ∈ xs → D)) (ds : List D) :
    (coloursCounted x xs tails ds).values =
      ds.flatMap (fun d => tails.map (List.Pi.cons x xs d)) := by
  induction ds <;> simp [coloursCounted, *]

@[simp] theorem work_coloursCounted {A : Type u} {D : Type v} [DecidableEq A]
    (x : A) (xs : List A) (tails : List (∀ i, i ∈ xs → D)) (ds : List D) :
    (coloursCounted x xs tails ds).work =
      colourAssignmentWork ds.length tails.length := by
  induction ds with
  | nil => simp [coloursCounted, colourAssignmentWork]
  | cons d ds ih =>
      ext <;> simp [coloursCounted, ih, mapAssignmentWork, appendAssignmentWork,
        colourAssignmentWork, AssignmentWork.add, AssignmentWork.step] <;> ring

/-- Reuse the recursively constructed tail list for all colours at this coordinate. -/
def piCounted {A : Type u} {D : Type v} [DecidableEq A] :
    (xs : List A) → List D → AssignmentListResult (∀ i, i ∈ xs → D)
  | [], _ => ⟨[List.Pi.nil (fun _ => D)], ⟨1, 1, 0, 0, 0, 1⟩⟩
  | x :: xs, ds =>
      let tails := piCounted xs ds
      let rows := coloursCounted x xs tails.values ds
      ⟨rows.values, (tails.work.add rows.work).step 0 0⟩

@[simp] theorem values_piCounted {A : Type u} {D : Type v} [DecidableEq A]
    (xs : List A) (ds : List D) :
    (piCounted xs ds).values = List.pi xs (fun _ => ds) := by
  induction xs <;> simp [piCounted, List.pi_cons, *]

@[simp] theorem length_values_piCounted {A : Type u} {D : Type v} [DecidableEq A]
    (xs : List A) (ds : List D) :
    (piCounted xs ds).values.length = ds.length ^ xs.length := by
  simp [length_pi_uniform]

@[simp] theorem work_piCounted {A : Type u} {D : Type v} [DecidableEq A]
    (xs : List A) (ds : List D) :
    (piCounted xs ds).work = piAssignmentWork xs.length ds.length := by
  induction xs <;> simp [piCounted, piAssignmentWork, length_pi_uniform, *]

/-- Construct a total assignment closure for every dependent assignment. -/
def totalizeCounted {A : Type u} {D : Type v}
    (xs : List A) (complete : ∀ i, i ∈ xs) :
    List (∀ i, i ∈ xs → D) → AssignmentListResult (A → D)
  | [] => ⟨[], {listCases := 1, nilResults := 1}⟩
  | f :: fs =>
      let tail := totalizeCounted xs complete fs
      ⟨(fun i => f i (complete i)) :: tail.values, tail.work.step 1 1⟩

@[simp] theorem values_totalizeCounted {A : Type u} {D : Type v}
    (xs : List A) (complete : ∀ i, i ∈ xs) (fs : List (∀ i, i ∈ xs → D)) :
    (totalizeCounted xs complete fs).values = fs.map (fun f i => f i (complete i)) := by
  induction fs <;> simp [totalizeCounted, *]

@[simp] theorem work_totalizeCounted {A : Type u} {D : Type v}
    (xs : List A) (complete : ∀ i, i ∈ xs) (fs : List (∀ i, i ∈ xs → D)) :
    (totalizeCounted xs complete fs).work = mapAssignmentWork fs.length := by
  induction fs <;> simp [totalizeCounted, *, mapAssignmentWork, AssignmentWork.step]

/-- Equality of the coordinate list transports the dependent product and its
membership-erasing map together. The completeness proofs are irrelevant. -/
theorem totalizedPi_congr {A : Type u} {D : Type v} [DecidableEq A]
    (xs ys : List A) (h : xs = ys) (hx : ∀ i, i ∈ xs) (hy : ∀ i, i ∈ ys)
    (ds : List D) :
    (List.pi xs (fun _ => ds)).map (fun f i => f i (hx i)) =
      (List.pi ys (fun _ => ds)).map (fun f i => f i (hy i)) := by
  subst ys
  rfl

end AssignmentEnumeration

open AssignmentEnumeration

/-- Generate every `Fin n → Fin q` assignment and accumulate its actual construction
observations. No caller enumeration list or claimed enumeration equality is needed. -/
def enumerateFinAssignments (n q : Nat) : AssignmentResult n q :=
  let coordinates := generateFinRange n
  let colours := generateFinRange q
  let dependent := piCounted coordinates.values colours.values
  let total := totalizeCounted coordinates.values (fun i => mem_generateFinRange n i)
    dependent.values
  ⟨total.values,
    ((AssignmentWork.ofRange coordinates.cost).add (AssignmentWork.ofRange colours.cost)).add
      (dependent.work.add total.work)⟩

/-- The output preserves the exact established Cartesian-product order. -/
@[simp] theorem values_enumerateFinAssignments (n q : Nat) :
    (enumerateFinAssignments n q).values = enumerateAssignments (Fin n) (Fin q) := by
  simp only [enumerateFinAssignments, values_totalizeCounted, values_piCounted,
    enumerateAssignments, generateFinRange_values, enumerateValues_fin]
  apply totalizedPi_congr
  simp

@[simp] theorem length_values_enumerateFinAssignments (n q : Nat) :
    (enumerateFinAssignments n q).values.length = q ^ n := by
  simp

theorem nodup_values_enumerateFinAssignments (n q : Nat) :
    (enumerateFinAssignments n q).values.Nodup := by
  simp

@[simp] theorem mem_values_enumerateFinAssignments (n q : Nat) (a : Fin n → Fin q) :
    a ∈ (enumerateFinAssignments n q).values := by
  simp

/-- Exact work is derived from the helper recursions and the actual range generators. -/
@[simp] theorem work_enumerateFinAssignments (n q : Nat) :
    (enumerateFinAssignments n q).work = assignmentEnumerationWork n q := by
  simp [enumerateFinAssignments, assignmentEnumerationWork, rangeAssignmentWork,
    AssignmentWork.ofRange, AssignmentWork.add, length_pi_uniform,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem piAssignmentWork_zero (q : Nat) :
    piAssignmentWork 0 q = ⟨1, 1, 0, 0, 0, 1⟩ := rfl

theorem piAssignmentWork_succ (n q : Nat) :
    piAssignmentWork (n + 1) q =
      ((piAssignmentWork n q).add (colourAssignmentWork q (q ^ n))).step 0 0 := rfl

theorem cases_piAssignmentWork_succ (n q : Nat) :
    (piAssignmentWork (n + 1) q).listCases =
      (piAssignmentWork n q).listCases + q * (2 * q ^ n + 3) + 2 := by
  simp [piAssignmentWork, colourAssignmentWork, AssignmentWork.add, AssignmentWork.step]
  omega

theorem cons_piAssignmentWork_succ (n q : Nat) :
    (piAssignmentWork (n + 1) q).listCons =
      (piAssignmentWork n q).listCons + 2 * q * q ^ n := by
  simp [piAssignmentWork, colourAssignmentWork, AssignmentWork.add, AssignmentWork.step]

theorem closures_piAssignmentWork_succ (n q : Nat) :
    (piAssignmentWork (n + 1) q).assignmentClosures =
      (piAssignmentWork n q).assignmentClosures + q * q ^ n := by
  simp [piAssignmentWork, colourAssignmentWork, AssignmentWork.add, AssignmentWork.step]

@[simp] theorem rangeTests_piAssignmentWork (n q : Nat) :
    (piAssignmentWork n q).rangeTests = 0 := by
  induction n <;> simp [piAssignmentWork, colourAssignmentWork,
    AssignmentWork.add, AssignmentWork.step, *]

@[simp] theorem natIncrements_piAssignmentWork (n q : Nat) :
    (piAssignmentWork n q).natIncrements = 0 := by
  induction n <;> simp [piAssignmentWork, colourAssignmentWork,
    AssignmentWork.add, AssignmentWork.step, *]

@[simp] theorem nils_piAssignmentWork (n q : Nat) :
    (piAssignmentWork n q).nilResults = n * (q + 1) + 1 := by
  induction n <;> simp [piAssignmentWork, colourAssignmentWork,
    AssignmentWork.add, AssignmentWork.step, *, Nat.add_mul]
  omega

@[simp] theorem rangeTests_enumerateFinAssignments (n q : Nat) :
    (enumerateFinAssignments n q).work.rangeTests = n + q + 2 := by
  simp [assignmentEnumerationWork, rangeAssignmentWork, mapAssignmentWork, AssignmentWork.add]

@[simp] theorem natIncrements_enumerateFinAssignments (n q : Nat) :
    (enumerateFinAssignments n q).work.natIncrements = n + q := by
  simp [assignmentEnumerationWork, rangeAssignmentWork, mapAssignmentWork, AssignmentWork.add]

@[simp] theorem nils_enumerateFinAssignments (n q : Nat) :
    (enumerateFinAssignments n q).work.nilResults = n * (q + 1) + 4 := by
  simp [assignmentEnumerationWork, rangeAssignmentWork, mapAssignmentWork, AssignmentWork.add]
  omega

/-- An empty coordinate set still yields its unique assignment, for every domain. -/
theorem values_enumerateFinAssignments_zero (q : Nat) :
    (enumerateFinAssignments 0 q).values = [Fin.elim0] := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    exact Subsingleton.elim _ _

theorem work_enumerateFinAssignments_zero (q : Nat) :
    (enumerateFinAssignments 0 q).work = ⟨3, q + 2, 1, q + 2, q, 4⟩ := by
  simp [assignmentEnumerationWork, rangeAssignmentWork, mapAssignmentWork,
    AssignmentWork.add]

/-- For an empty colour domain the implementation still constructs its recursive
tails; these discarded intermediate constructions are included in the work. -/
theorem piAssignmentWork_emptyDomain (n : Nat) :
    piAssignmentWork n 0 = ⟨2 * n + 1, 1, 0, 0, 0, n + 1⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      ext <;> simp [piAssignmentWork, ih, colourAssignmentWork,
        AssignmentWork.add, AssignmentWork.step]
      omega

theorem values_enumerateFinAssignments_emptyDomain (n : Nat) :
    (enumerateFinAssignments (n + 1) 0).values = [] := by
  apply List.eq_nil_of_length_eq_zero
  simp

theorem work_enumerateFinAssignments_emptyDomain (n : Nat) :
    (enumerateFinAssignments (n + 1) 0).work =
      ⟨2 * n + 4, n + 2, 0, n + 3, n + 1, n + 5⟩ := by
  ext <;> simp [assignmentEnumerationWork, rangeAssignmentWork, mapAssignmentWork,
    piAssignmentWork_emptyDomain, AssignmentWork.add] <;> omega

theorem piAssignmentWork_singletonDomain (n : Nat) :
    piAssignmentWork n 1 = ⟨7 * n + 1, 2 * n + 1, n, 0, 0, 2 * n + 1⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      ext <;> simp [piAssignmentWork, ih, colourAssignmentWork,
        AssignmentWork.add, AssignmentWork.step] <;> omega

theorem work_enumerateFinAssignments_singletonDomain (n : Nat) :
    (enumerateFinAssignments n 1).work =
      ⟨7 * n + 3, 3 * n + 3, n + 1, n + 3, n + 1, 2 * n + 4⟩ := by
  ext <;> simp [assignmentEnumerationWork, rangeAssignmentWork, mapAssignmentWork,
    piAssignmentWork_singletonDomain, AssignmentWork.add] <;> omega

end Counting.Algorithm.VariableEliminationWork
