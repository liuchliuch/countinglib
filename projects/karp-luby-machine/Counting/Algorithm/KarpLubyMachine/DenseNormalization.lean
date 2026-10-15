import Counting.Algorithm.KarpLuby.Cost
import Counting.Algorithm.KarpLuby.Encoding

/-!
# Materialized normalization of an explicit DNF

The output of this implementation is a list of dense lists of optional Booleans.
No function-update chains are stored. Costs count visited list cells, constructors,
and Boolean tests. Index arithmetic is still an intermediate operation here;
this module does not identify this count with finite-machine bit time.
-/
namespace Counting.Algorithm.KarpLubyMachine.DenseNormalization

open Counting.Algorithm.KarpLuby
open DNF

abbrev Cells := List (Option Bool)

/-- Interpretation is used in correctness statements, not as the stored table. -/
def denote (n : ℕ) (xs : Cells) : Clause n := fun i => xs[i.val]?.join

/-- Allocate every explicit coordinate, including variables absent from literals. -/
def allocate : ℕ → Cost.Evaluation Cells
  | 0 => ⟨[], 1⟩
  | n + 1 => let r := allocate n; ⟨none :: r.value, r.operations + 1⟩

@[simp] theorem allocate_value (n : ℕ) : (allocate n).value = List.replicate n none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allocate, ih, List.replicate_succ]

@[simp] theorem allocate_operations (n : ℕ) : (allocate n).operations = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allocate, ih]

@[simp] theorem denote_allocate (n : ℕ) : denote n (allocate n).value = fun _ => none := by
  funext i
  simp [denote, i.isLt]

/-- A checked literal write scans to its coordinate, rejects conflicts, and
reconstructs the visited prefix. It does not perform a unit-cost random access. -/
def write : ℕ → Bool → Cells → Cost.Evaluation (Option Cells)
  | _, _, [] => ⟨none, 1⟩
  | 0, b, none :: xs => ⟨some (some b :: xs), 2⟩
  | 0, b, some old :: xs =>
      if old = b then ⟨some (some old :: xs), 3⟩ else ⟨none, 3⟩
  | j + 1, b, x :: xs =>
      let r := write j b xs
      ⟨r.value.map (x :: ·), r.operations + 2⟩

/-- The exact value of a checked scan is the usual bounded list replacement. -/
theorem write_value (xs : Cells) (j : ℕ) (b : Bool) (hj : j < xs.length) :
    (write j b xs).value =
      match xs[j]?.join with
      | none => some (xs.set j (some b))
      | some old => if old = b then some xs else none := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero =>
      cases x with
      | none => rfl
      | some old => simp only [write]; split <;> simp_all
    | succ j =>
      have h : j < xs.length := by simpa using hj
      simp only [write]
      rw [ih j h]
      cases he : xs[j]?.join <;> simp [he]

/-- Every successful write preserves the materialized table length. -/
theorem write_length (xs : Cells) (j : ℕ) (b : Bool) (ys : Cells)
    (h : (write j b xs).value = some ys) : ys.length = xs.length := by
  induction xs generalizing j ys with
  | nil => simp [write] at h
  | cons x xs ih =>
    cases j with
    | zero =>
      cases x with
      | none => simpa [write] using congrArg (Option.map List.length) h.symm
      | some old =>
        simp only [write] at h
        split at h
        · cases h; rfl
        · contradiction
    | succ j =>
      simp only [write] at h
      obtain ⟨tail, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [ih j tail ht]

/-- All inputs, even invalid indices, have a linear scan cost. -/
theorem write_operations_le (xs : Cells) (j : ℕ) (b : Bool) :
    (write j b xs).operations ≤ 2 * xs.length + 3 := by
  induction xs generalizing j with
  | nil => simp [write]
  | cons x xs ih =>
    cases j with
    | zero => cases x <;> simp [write]; split <;> simp
    | succ j => have h := ih j; simp only [write, List.length_cons]; omega

theorem denote_set {n : ℕ} (xs : Cells) (hxs : xs.length = n)
    (i : Fin n) (b : Bool) :
    denote n (xs.set i.val (some b)) = Function.update (denote n xs) i (some b) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [denote, List.getElem?_set_self (by omega : i.val < xs.length)]
  · have hv : i.val ≠ j.val := by intro he; exact h (Fin.ext he.symm)
    simp [denote, List.getElem?_set_ne hv, Function.update_of_ne h]

/-- Refinement preserves the exact ambient variable type and literal order. -/
theorem write_refines {n : ℕ} (xs : Cells) (hxs : xs.length = n) (l : Fin n × Bool) :
    ((write l.1.val l.2 xs).value.map (denote n)) = insertLiteral (denote n xs) l := by
  rw [write_value xs l.1.val l.2 (by have := l.1.isLt; omega)]
  unfold insertLiteral
  change (match denote n xs l.1 with
    | none => some (xs.set l.1.val (some l.2))
    | some old => if old = l.2 then some xs else none).map (denote n) = _
  cases hc : denote n xs l.1 with
  | none => simp [denote_set xs hxs]
  | some old => split <;> simp_all

/-- Tail-first normalization exactly matches R1, materializing a fresh table
for each term and skipping prefix writes after a conflicting suffix. -/
def normalize (n : ℕ) : RawTerm n → Cost.Evaluation (Option Cells)
  | [] => let a := allocate n; ⟨some a.value, a.operations + 1⟩
  | l :: t =>
      let r := normalize n t
      match r.value with
      | none => ⟨none, r.operations + 1⟩
      | some xs =>
          let w := write l.1.val l.2 xs
          ⟨w.value, r.operations + w.operations + 1⟩

/-- Successful terms retain one cell for every explicitly declared variable. -/
theorem normalize_length {n : ℕ} (t : RawTerm n) (xs : Cells)
    (h : (normalize n t).value = some xs) : xs.length = n := by
  induction t generalizing xs with
  | nil => simpa [normalize] using congrArg (Option.map List.length) h.symm
  | cons l t ih =>
    simp only [normalize] at h
    cases hr : (normalize n t).value with
    | none => simp [hr] at h
    | some ys =>
      simp only [hr] at h
      exact (write_length ys l.1.val l.2 xs h).trans (ih ys hr)

@[simp] theorem normalize_refines {n : ℕ} (t : RawTerm n) :
    (normalize n t).value.map (denote n) = DNF.normalize t := by
  induction t with
  | nil =>
    change some (denote n (allocate n).value) = some (fun _ => none)
    rw [denote_allocate]
  | cons l t ih =>
    simp only [DNF.normalize, ← ih, normalize]
    cases hr : (normalize n t).value with
    | none => rfl
    | some xs =>
      simpa using write_refines xs (normalize_length t xs hr) l

/-- Allocation and every executed prefix traversal are included. -/
theorem normalize_operations_le {n : ℕ} (t : RawTerm n) :
    (normalize n t).operations ≤ n + 2 + t.length * (2 * n + 4) := by
  induction t with
  | nil => simp [normalize]
  | cons l t ih =>
    simp only [normalize, List.length_cons]
    cases hr : (normalize n t).value with
    | none => simp only; nlinarith
    | some xs =>
      have hl := normalize_length t xs hr
      have hw := write_operations_le xs l.1.val l.2
      simp only
      nlinarith

/-- Materialized list normalization; contradictions are dropped, whereas
repeated clauses and their order are preserved. -/
def formula (n : ℕ) : Formula n → Cost.Evaluation (List Cells)
  | [] => ⟨[], 1⟩
  | t :: ts =>
      let r := normalize n t
      let rest := formula n ts
      match r.value with
      | none => ⟨rest.value, r.operations + rest.operations + 1⟩
      | some xs => ⟨xs :: rest.value, r.operations + rest.operations + 2⟩

@[simp] theorem formula_refines {n : ℕ} (f : Formula n) :
    (formula n f).value.map (denote n) = normalizeFormula f := by
  induction f with
  | nil => rfl
  | cons t ts ih =>
    simp only [formula, normalizeFormula, List.filterMap_cons]
    have ht := normalize_refines t
    cases hr : (normalize n t).value with
    | none =>
      simp only [hr, Option.map_none] at ht
      simp [← ht, ih, normalizeFormula]
    | some xs =>
      simp only [hr, Option.map_some] at ht
      simp [← ht, ih, normalizeFormula]

/-- Every retained table has the same explicit ambient variable count. -/
theorem formula_lengths {n : ℕ} (f : Formula n) :
    ∀ xs ∈ (formula n f).value, xs.length = n := by
  induction f with
  | nil => simp [formula]
  | cons t ts ih =>
    simp only [formula]
    cases hr : (normalize n t).value with
    | none => exact ih
    | some xs =>
      intro ys hy
      simp only [List.mem_cons] at hy
      rcases hy with he | hy
      · subst ys
        exact normalize_length t xs hr
      · exact ih ys hy

theorem formula_count_le {n : ℕ} (f : Formula n) : (formula n f).value.length ≤ f.length := by
  calc
    (formula n f).value.length = ((formula n f).value.map (denote n)).length :=
      (List.length_map ..).symm
    _ = (normalizeFormula f).length := congrArg List.length (formula_refines f)
    _ ≤ f.length := List.length_filterMap_le DNF.normalize f

/-- Whole normalization cost, with both term and literal occurrences charged. -/
theorem formula_operations_le {n : ℕ} (f : Formula n) :
    (formula n f).operations ≤
      1 + f.length * (n + 4) + (f.map List.length).sum * (2 * n + 4) := by
  induction f with
  | nil => simp [formula]
  | cons t ts ih =>
    have ht := normalize_operations_le t
    simp only [formula, List.length_cons, List.map_cons, List.sum_cons]
    cases (normalize n t).value <;> simp only <;> nlinarith

/-- The request codec explicitly pays for unused variables and all occurrences,
yielding a quadratic bound for this materialized preprocessing stage. -/
theorem formula_operations_le_input_length {n : ℕ} (f : Formula n) :
    (formula n f).operations ≤
      let L := (Encoding.encodeInput ⟨n, f⟩).length
      1 + L * (L + 4) + L * (2 * L + 4) := by
  have hn := Encoding.variables_le_input_length ⟨n, f⟩
  have hm := Encoding.terms_le_input_length ⟨n, f⟩
  have ht := Encoding.literals_le_input_length ⟨n, f⟩
  apply (formula_operations_le f).trans
  dsimp at hn hm ht ⊢
  gcongr

/-- Dense storage contains at most `n * numberOfTerms` ternary cells. -/
theorem formula_storage_le {n : ℕ} (f : Formula n) :
    (((formula n f).value).map List.length).sum ≤ f.length * n := by
  have aux (as : List Cells) (h : ∀ xs ∈ as, xs.length = n) :
      (as.map List.length).sum = as.length * n := by
    induction as with
    | nil => simp
    | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp [hx, ht, Nat.add_mul, Nat.add_comm]
  have he := aux (formula n f).value (formula_lengths f)
  rw [he]
  exact Nat.mul_le_mul_right n (formula_count_le f)

end Counting.Algorithm.KarpLubyMachine.DenseNormalization
