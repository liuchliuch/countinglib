import PlanarHom.OccurrenceKasteleynOrientationIteration

/-!
# Finite face-table orientation

This interface exposes the canonical occurrence-aware peeling program and its
forward-loop/reverse-fold implementation. A table retains the order and
multiplicity of every boundary dart. Lookup uses the first row of a face label.
The program and output bounds apply to every raw table; clockwise-odd correctness
uses the stated compatible dual-incidence and reachability promises.

The results here concern the literal program, its output, and face semantics.
The encoded polynomial-time machine is provided by a separate module.
-/

namespace Counting.Algorithm.FKT.Orientation

open PlanarHom.MultiGraph.Kasteleyn

/-- A labelled row of directed edge occurrences. -/
abbrev RawFace := PlanarHom.MultiGraph.Kasteleyn.RawFace

/-- Ordered raw rows; neither dart occurrences nor face labels are deduplicated. -/
abbrev Table := List RawFace

/-- The actual recursive table-to-toggle-log program. -/
def orientationLog (table : Table) : List ℕ := computeOrientation table

/-- The bounded forward loop followed by reverse repair. -/
def iterativeLog (table : Table) : List ℕ := computeOrientationIterative table

/-- A toggle history starts with every edge directed forward. -/
def orientation (table : Table) : ℕ → Bool := logOrientation (orientationLog table)

/-- Equality holds on all raw tables, including conflicting duplicate labels. -/
theorem iterativeLog_eq (table : Table) : iterativeLog table = orientationLog table :=
  computeOrientationIterative_eq_computeOrientation table

/-- The public result is exactly the fold over the actual computed pivot stack. -/
theorem orientationLog_eq_repairFold (table : Table) :
    orientationLog table = (peelState table).2.2.foldl (repairLog table) [] :=
  (computeOrientationIterative_eq_computeOrientation table).symm

/-- No more than one toggle is returned per input row, without validity assumptions. -/
theorem orientationLog_length_le (table : Table) :
    (orientationLog table).length ≤ table.length :=
  computeOrientation_length_le table

/-- Every returned index comes from a literal dart in an original input row. -/
theorem orientationLog_mem_source (table : Table) {e : ℕ}
    (he : e ∈ orientationLog table) :
    ∃ f ds, (f, ds) ∈ table ∧ ∃ a ∈ ds, a.1 = e :=
  computeOrientation_mem_source table he

/-- Repair retains a sublist of the chronological pivot indices. -/
theorem orientationLog_sublist_pivots (table : Table) :
    (orientationLog table).Sublist (((peelState table).2.2.map Prod.snd).reverse) := by
  rw [orientationLog_eq_repairFold]
  simpa only [List.append_nil] using
    repairLog_foldl_sublist table (peelState table).2.2 []

/-- An edge absent from every input dart keeps its initial forward direction. -/
theorem orientation_eq_true_of_unused (table : Table) (e : ℕ)
    (he : ∀ f ds, (f, ds) ∈ table → ∀ a ∈ ds, a.1 ≠ e) :
    orientation table e = true := by
  apply logOrientation_of_not_mem
  intro hmem
  obtain ⟨f, ds, hrow, a, ha, hae⟩ := orientationLog_mem_source table hmem
  exact he f ds hrow a ha hae

/-- Full finite-dual contract: only listed faces must be root-reachable, and the
root is omitted. No solved orientation or pivot order is supplied by the caller. -/
theorem orientation_faceOdd (D : DualIncidence ℕ ℕ)
    (boundary : Boundaries ℕ ℕ) (hc : D.Compatible boundary)
    (root : ℕ) (fs : List ℕ)
    (hconn : ∀ f ∈ fs, Relation.ReflTransGen D.Adj root f)
    (hn : fs.Nodup) (hr : root ∉ fs) :
    ∀ f ∈ fs, FaceOdd (orientation (faceTable boundary fs)) (boundary f) :=
  computeOrientation_faceOdd D boundary hc root fs hconn hn hr

/-- Clockwise oddness counts literal agreements, including repeated traversals. -/
theorem orientation_odd_agreements (D : DualIncidence ℕ ℕ)
    (boundary : Boundaries ℕ ℕ) (hc : D.Compatible boundary)
    (root : ℕ) (fs : List ℕ)
    (hconn : ∀ f ∈ fs, Relation.ReflTransGen D.Adj root f)
    (hn : fs.Nodup) (hr : root ∉ fs) (f : ℕ) (hf : f ∈ fs) :
    ((boundary f).countP (fun a => orientation (faceTable boundary fs) a.1 == a.2)).bodd =
      true :=
  (faceOdd_iff_odd_agreementCount _ _).mp
    (orientation_faceOdd D boundary hc root fs hconn hn hr f hf)

end Counting.Algorithm.FKT.Orientation
