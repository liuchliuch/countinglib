import Counting.Model.Graph

/-!
# Kernel-checked graph-to-CSP edge cases

The values are first proved on the graph side using finite-sum equivalences,
then transported through `MultiGraph.partition_toOpenInstance`. In particular,
none of these checks evaluates the adapter's noncomputable list enumeration.
The combined example simultaneously has a loop, parallel edge occurrences,
an isolated vertex, and different weight tables at all three vertices.
-/

open scoped BigOperators

noncomputable section

open Classical

namespace Counting.Examples.Graph

open Model

/-- The unique assignment on the empty boundary. -/
def boundary (D : Type) : Empty → D := Empty.elim

/-- A nonsymmetric interaction table detects the order of the endpoints. -/
def interaction (x y : Bool) : Nat :=
  if x then (if y then 11 else 7) else (if y then 5 else 2)

/-- Weights for the one-vertex isolated example. -/
def isolatedWeight (_ : Unit) (x : Bool) : Nat := if x then 3 else 2

/-- One vertex and one loop edge occurrence. -/
def loopGraph : MultiGraph Unit Unit := ⟨fun _ => (), fun _ => ()⟩

/-- Two distinct edge occurrences sharing the same ordered endpoints. -/
def parallelGraph : MultiGraph Bool Bool := ⟨fun _ => false, fun _ => true⟩

/-- A vertex exists even though it belongs to no edge occurrence. -/
def isolatedGraph : MultiGraph Unit Empty := ⟨Empty.elim, Empty.elim⟩

/-- Both the vertex type and the edge type are empty. -/
def emptyGraph : MultiGraph Empty Empty := ⟨Empty.elim, Empty.elim⟩

/-- `none` is isolated; `some false` carries a loop and is the source of
both parallel edges to `some true`. -/
def combinedGraph : MultiGraph (Option Bool) (Option Bool) where
  src _ := some false
  dst e := match e with
    | none => some false
    | some _ => some true

/-- The three vertices have different unary weight tables. -/
def combinedWeight (v : Option Bool) (x : Bool) : Nat :=
  match v with
  | none => if x then 19 else 17
  | some false => if x then 3 else 2
  | some true => if x then 7 else 5

-- Match the generic adapter's classical equality instances. The proofs below
-- use finite-sum equivalences rather than reducing those instances.
local instance : DecidableEq Unit := fun _ _ => Classical.propDecidable _
local instance : DecidableEq Bool := fun _ _ => Classical.propDecidable _
local instance : DecidableEq Empty := fun _ _ => Classical.propDecidable _
local instance : DecidableEq (Option Bool) := fun _ _ => Classical.propDecidable _

private theorem sum_unit_assignments (f : (Unit → Bool) → Nat) :
    (∑ a, f a) = ∑ x : Bool, f (fun _ => x) :=
  ((Equiv.funUnique Unit Bool).symm.sum_comp f).symm

private theorem sum_bool_assignments (f : (Bool → Bool) → Nat) :
    (∑ a, f a) = ∑ x : Bool, ∑ y : Bool, f (fun b => if b then y else x) := by
  rw [← (Equiv.boolArrowEquivProd Bool).symm.sum_comp f, Fintype.sum_prod_type]
  congr 1
  funext x
  congr 1
  funext y
  congr 1
  funext b
  cases b <;> simp [Equiv.boolArrowEquivProd]

private theorem sum_option_assignments (f : (Option Bool → Bool) → Nat) :
    (∑ a, f a) = ∑ x : Bool, ∑ b : Bool → Bool,
      f (fun v => match v with | none => x | some i => b i) := by
  rw [← (Equiv.piOptionEquivProd (β := fun _ : Option Bool => Bool)).symm.sum_comp f,
    Fintype.sum_prod_type]
  congr 1
  funext x
  congr 1
  funext b
  congr 1
  funext v
  cases v <;> rfl

/-- A loop sees only the two diagonal entries: `2 + 11`. -/
theorem loop_partition : loopGraph.partition interaction (fun _ _ => 1) = 13 := by
  unfold MultiGraph.partition
  rw [sum_unit_assignments]
  simp [MultiGraph.assignmentWeight, interaction]

theorem loop_csp_partition :
    (loopGraph.toOpenInstance interaction (fun _ _ => 1)).partition (boundary Bool) = 13 := by
  rw [MultiGraph.partition_toOpenInstance, loop_partition]

/-- Each parallel edge contributes, producing the sum of squared entries. -/
theorem parallel_partition : parallelGraph.partition interaction (fun _ _ => 1) = 199 := by
  unfold MultiGraph.partition
  rw [sum_bool_assignments]
  simp [MultiGraph.assignmentWeight, parallelGraph, interaction]

theorem parallel_csp_partition :
    (parallelGraph.toOpenInstance interaction (fun _ _ => 1)).partition (boundary Bool) = 199 := by
  rw [MultiGraph.partition_toOpenInstance, parallel_partition]

/-- Summation retains an isolated vertex and its unary table: `2 + 3`. -/
theorem isolated_partition : isolatedGraph.partition interaction isolatedWeight = 5 := by
  unfold MultiGraph.partition
  rw [sum_unit_assignments]
  simp [MultiGraph.assignmentWeight, isolatedWeight]

theorem isolated_csp_partition :
    (isolatedGraph.toOpenInstance interaction isolatedWeight).partition (boundary Bool) = 5 := by
  rw [MultiGraph.partition_toOpenInstance, isolated_partition]

/-- There is exactly one assignment on the empty vertex set. -/
theorem empty_partition : emptyGraph.partition interaction (fun v => v.elim) = 1 := by
  simp [MultiGraph.partition, MultiGraph.assignmentWeight]

theorem empty_csp_partition :
    (emptyGraph.toOpenInstance interaction (fun v => v.elim)).partition (boundary Bool) = 1 := by
  rw [MultiGraph.partition_toOpenInstance, empty_partition]

/-- The empty graph remains valid over the empty domain. -/
theorem empty_domain_partition :
    emptyGraph.partition (fun x : Empty => x.elim) (fun v => v.elim) = (1 : Nat) := by
  simp [MultiGraph.partition, MultiGraph.assignmentWeight]

theorem empty_domain_csp_partition :
    (emptyGraph.toOpenInstance (fun x : Empty => x.elim) (fun v => v.elim)).partition
      (boundary Empty) = (1 : Nat) := by
  rw [MultiGraph.partition_toOpenInstance, empty_domain_partition]

/-- The isolated vertex contributes `36`; the other two vertices, loop, and
parallel edges contribute `36816`. Their combined sum is `1325376`. -/
theorem combined_partition : combinedGraph.partition interaction combinedWeight = 1325376 := by
  unfold MultiGraph.partition
  rw [sum_option_assignments]
  simp only [sum_bool_assignments, Fintype.sum_bool]
  simp [MultiGraph.assignmentWeight, Fintype.prod_option,
    combinedGraph, combinedWeight, interaction]

theorem combined_csp_partition :
    (combinedGraph.toOpenInstance interaction combinedWeight).partition (boundary Bool) =
      1325376 := by
  rw [MultiGraph.partition_toOpenInstance, combined_partition]

/-- The loop becomes one binary occurrence whose two ports use the same vertex. -/
theorem loop_repeated_scope :
    (loopGraph.edgeOccurrence interaction (fun _ _ => 1) ()).scope (0 : Fin 2) =
      (loopGraph.edgeOccurrence interaction (fun _ _ => 1) ()).scope (1 : Fin 2) := by
  simp [loopGraph]

/-- Both parallel edge identifiers produce the same occurrence, so retaining
both in the adapter is necessary to obtain the squared factors. -/
theorem parallel_same_occurrence :
    parallelGraph.edgeOccurrence interaction (fun _ _ => 1) false =
      parallelGraph.edgeOccurrence interaction (fun _ _ => 1) true := rfl

/-- The asymmetric entry at the ordered endpoints is `5`, not `7`. -/
theorem parallel_ordered_eval :
    (parallelGraph.edgeOccurrence interaction (fun _ _ => 1) false).eval
      (Sum.elim (boundary Bool) id) = 5 := by
  simp [parallelGraph, interaction]

/-- No edge touches the `none` vertex. -/
theorem combined_isolated_vertex (e : Option Bool) :
    combinedGraph.src e ≠ none ∧ combinedGraph.dst e ≠ none := by
  cases e <;> simp [combinedGraph]

/-- The unary resource associated with each vertex retains its own weight. -/
theorem combined_distinct_vertex_weights :
    combinedWeight none false = 17 ∧ combinedWeight (some false) false = 2 ∧
      combinedWeight (some true) false = 5 := by
  decide

theorem loop_occurrence_count :
    (loopGraph.toOpenInstance interaction (fun _ _ => 1)).occurrences.length = 2 := by
  simp

theorem parallel_occurrence_count :
    (parallelGraph.toOpenInstance interaction (fun _ _ => 1)).occurrences.length = 4 := by
  simp

theorem isolated_occurrence_count :
    (isolatedGraph.toOpenInstance interaction isolatedWeight).occurrences.length = 1 := by
  simp

theorem empty_occurrence_count :
    (emptyGraph.toOpenInstance interaction (fun v => v.elim)).occurrences.length = 0 := by
  simp

theorem combined_occurrence_count :
    (combinedGraph.toOpenInstance interaction combinedWeight).occurrences.length = 6 := by
  simp

end Counting.Examples.Graph
