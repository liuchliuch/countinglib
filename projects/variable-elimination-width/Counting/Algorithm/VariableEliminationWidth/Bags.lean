import Counting.Algorithm.VariableElimination.Bucket
import Mathlib.Data.Finset.Card

/-!
# Supplied rooted bag trees

A tree is encoded by successive leaf attachments to a concrete parent index.
The attachment condition is about intersections of input bags only. It contains
neither a vertex elimination order nor a condition on executable buckets.
-/

namespace Counting.Algorithm.VariableEliminationWidth

open Counting.Algorithm.VariableElimination

variable {V D R : Type} [DecidableEq V]

/-- Vertices appearing in a bag list. -/
def bagUnion (bags : List (Finset V)) : Finset V := bags.foldr (· ∪ ·) ∅

@[simp] theorem mem_bagUnion (v : V) (bags : List (Finset V)) :
    v ∈ bagUnion bags ↔ ∃ bag ∈ bags, v ∈ bag := by
  induction bags with
  | nil => simp [bagUnion]
  | cons bag bags ih =>
      change v ∈ bag ∪ bagUnion bags ↔ _
      rw [Finset.mem_union, ih]
      simp

/-- A real finite rooted tree represented by leaf attachments. `parent` is data;
the local overlap condition says every old occurrence of a leaf vertex reaches
its parent. Root bags may be empty; the tree itself always has a root. -/
inductive BagTree : List (Finset V) → Type where
  | root (bag : Finset V) : BagTree [bag]
  | attach (bag : Finset V) {bags : List (Finset V)} (rest : BagTree bags)
      (parent : Fin bags.length)
      (overlap : ∀ other ∈ bags, bag ∩ other ⊆ bags.get parent) : BagTree (bag :: bags)

/-- A supplied width certificate concerns input bags, not dynamic buckets.
Every vertex, including an isolated one, must occur in an input bag. -/
structure Decomposition (V : Type) [DecidableEq V] (width : Nat) where
  bags : List (Finset V)
  tree : BagTree bags
  cover : ∀ v : V, ∃ bag ∈ bags, v ∈ bag
  card_le : ∀ bag ∈ bags, bag.card ≤ width + 1

/-- Input factor support fits in an input bag. Occurrences and port arities remain
in the original factors; this predicate only projects their distinct variables. -/
def Bagged (bags : List (Finset V)) (fs : List (Factor V D R)) : Prop :=
  ∀ f ∈ fs, ∃ bag ∈ bags, f.support ⊆ bag

/-- Variables unique to the current leaf bag. -/
def privateVertices (bag : Finset V) (rest : List (Finset V)) : Finset V :=
  bag \ bagUnion rest

@[simp] theorem mem_privateVertices (v : V) (bag : Finset V) (rest : List (Finset V)) :
    v ∈ privateVertices bag rest ↔ v ∈ bag ∧ ∀ other ∈ rest, v ∉ other := by
  simp [privateVertices]

/-- The supplied parent condition derives the separator property across the
leaf cut, for any two bags containing the same vertex. -/
theorem leaf_separator (bag : Finset V) (rest : List (Finset V))
    (parent : Fin rest.length)
    (overlap : ∀ other ∈ rest, bag ∩ other ⊆ rest.get parent)
    (v : V) (hv : v ∈ bag) (other : Finset V) (ho : other ∈ rest) (hvo : v ∈ other) :
    v ∈ rest.get parent := overlap other ho (Finset.mem_inter.mpr ⟨hv, hvo⟩)

/-- When a leaf has no private vertices it is contained in its actual parent,
so deleting that leaf preserves both coverage and factor containment. -/
theorem leaf_subset_parent (bag : Finset V) (rest : List (Finset V))
    (parent : Fin rest.length)
    (overlap : ∀ other ∈ rest, bag ∩ other ⊆ rest.get parent)
    (empty : privateVertices bag rest = ∅) : bag ⊆ rest.get parent := by
  intro v hv
  have hm : v ∈ bagUnion rest := by
    by_contra hn
    have : v ∈ privateVertices bag rest := Finset.mem_sdiff.mpr ⟨hv, hn⟩
    simp [empty] at this
  obtain ⟨other, ho, hvo⟩ := (mem_bagUnion v rest).mp hm
  exact leaf_separator bag rest parent overlap v hv other ho hvo

/-- Project a bag to the actual remaining-variable type after removing `v`. -/
def projectBag (v : V) (bag : Finset V) : Finset (Remaining v) :=
  bag.subtype (· ≠ v)

@[simp] theorem mem_projectBag (v : V) (bag : Finset V) (w : Remaining v) :
    w ∈ projectBag v bag ↔ w.val ∈ bag := Finset.mem_subtype

@[simp] theorem card_projectBag (v : V) (bag : Finset V) :
    (projectBag v bag).card = (bag.erase v).card := by
  rw [projectBag, Finset.card_subtype]
  congr 1
  ext w
  simp [and_comm]

theorem card_projectBag_le (v : V) (bag : Finset V) :
    (projectBag v bag).card ≤ bag.card := by
  rw [card_projectBag]
  exact Finset.card_le_card (Finset.erase_subset _ _)

end Counting.Algorithm.VariableEliminationWidth
