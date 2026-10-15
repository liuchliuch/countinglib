import Counting.GraphCSP.Reduction

/-!
# Concrete fixed-language graph-to-CSP clients

All values are proved with kernel-checked finite-sum equivalences and arithmetic.
The combined graph has a loop, two parallel ordered edges, and an isolated
vertex. Its fixed natural tables are deliberately asymmetric and nonconstant.
-/

open scoped BigOperators

noncomputable section

namespace Counting.GraphCSP.Examples

/-- The rows are `[2, 3]` and `[5, 7]`, in the order `false, true`. -/
def interaction (x y : Bool) : Nat :=
  if x then (if y then 7 else 5) else (if y then 3 else 2)

/-- Every vertex uses the same fixed table `[1, 2]`. -/
def unaryWeight (x : Bool) : Nat := if x then 2 else 1

/-- Vertex `0` has a loop and two directed edges to `1`; vertex `2` is isolated. -/
abbrev combinedGraph : Graph := ⟨3, [(0, 0), (0, 1), (0, 1)]⟩

/-- A vertex remains part of the input even when it has no incident edge. -/
abbrev isolatedGraph : Graph := ⟨1, []⟩

/-- The null graph has no vertices and no edge occurrences. -/
abbrev nullGraph : Graph := ⟨0, []⟩

/-- Explicit occurrences retain the loop and each parallel edge separately. -/
theorem combined_constraints : combinedGraph.toCSP.constraints =
    (show List (Constraint 3) from
      [.unary 0, .unary 1, .unary 2, .binary 0 0, .binary 0 1, .binary 0 1]) := rfl

theorem combined_vertex_count : combinedGraph.toCSP.n = 3 := rfl

theorem combined_constraint_count : combinedGraph.toCSP.constraints.length = 6 := by
  decide

theorem combined_occurrence_count :
    (combinedGraph.toCSP.toOpenInstance interaction unaryWeight).occurrences.length = 6 := by
  rw [CSP.toOpenInstance_occurrences_length, combined_constraint_count]

/-- No edge touches the isolated vertex; it nevertheless has a unary occurrence. -/
theorem combined_isolated_vertex :
    (∀ e ∈ combinedGraph.edges, e.1 ≠ 2 ∧ e.2 ≠ 2) ∧
      Constraint.unary (2 : Fin 3) ∈ combinedGraph.toCSP.constraints := by
  constructor
  · decide
  · rw [combined_constraints]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

/-- Repeated endpoints become repeated ports of one binary occurrence. -/
theorem combined_loop_scope :
    (Constraint.toOccurrence interaction unaryWeight (.binary (0 : Fin 3) 0)).scope (0 : Fin 2) =
      (Constraint.toOccurrence interaction unaryWeight (.binary (0 : Fin 3) 0)).scope (1 : Fin 2) :=
  Constraint.loop_scope interaction unaryWeight 0

/-- The two off-diagonal values distinguish an edge from its reversal. -/
theorem ordered_interaction : interaction false true = 3 ∧ interaction true false = 5 := by
  decide

/-- The first scope position uses the row of the interaction table. -/
theorem ordered_occurrence_eval :
    (Constraint.toOccurrence interaction unaryWeight (.binary (0 : Fin 2) 1)).eval
      (Sum.elim Empty.elim (fun i => decide (i = (1 : Fin 2)))) = 3 := by
  rw [Constraint.eval_binary]
  decide

/-- Every client uses exactly the two fixed resources, regardless of graph size. -/
theorem fixed_label_count : Fintype.card Bool = 2 := fixedLanguage_label_card

/-- Seven source symbols admit a fixed three-bit representation. -/
theorem source_alphabet_card : Fintype.card SourceSymbol = 7 := by decide

/-- The target alphabet has the same fixed cardinality. -/
theorem target_alphabet_card : Fintype.card TargetSymbol = 7 := by decide

theorem null_constraints : nullGraph.toCSP.constraints = [] := by decide

-- Match the equality instances used by S1's finite assignment enumeration.
local instance (n : Nat) : DecidableEq (Fin n) := fun _ _ => Classical.propDecidable _

private theorem sum_fin_succ_assignments (n : Nat)
    (f : (Fin (n + 1) → Bool) → Nat) :
    (∑ a, f a) = ∑ x : Bool, ∑ a : Fin n → Bool, f (Fin.cons x a) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp f,
    Fintype.sum_prod_type]
  rfl

/-- The isolated vertex contributes `3`; the other two vertices contribute
`8 + 36 + 350 + 1372 = 1766`, yielding `5298`. -/
theorem combined_partition : combinedGraph.partition interaction unaryWeight = 5298 := by
  unfold Graph.partition Model.MultiGraph.partition
  change (∑ a : Fin 3 → Bool,
    combinedGraph.toMultiGraph.assignmentWeight interaction (fun _ => unaryWeight) a) = 5298
  simp only [sum_fin_succ_assignments, Fintype.sum_bool]
  simp [Model.MultiGraph.assignmentWeight, Graph.toMultiGraph, combinedGraph,
    Fin.prod_univ_succ, interaction, unaryWeight]

/-- The fixed-language target has the same nontrivial value via the S1 bridge. -/
theorem combined_csp_partition :
    combinedGraph.toCSP.partition interaction unaryWeight = 5298 := by
  rw [Graph.partition_toCSP, combined_partition]

/-- An isolated vertex contributes the sum of its unary table. -/
theorem isolated_partition : isolatedGraph.partition interaction unaryWeight = 3 := by
  simp [Graph.partition_isolated, unaryWeight]

theorem isolated_csp_partition :
    isolatedGraph.toCSP.partition interaction unaryWeight = 3 := by
  rw [Graph.partition_toCSP, isolated_partition]

/-- The empty product and unique empty assignment give value one. -/
theorem null_partition : nullGraph.partition interaction unaryWeight = 1 := by
  exact Graph.partition_null _ _

theorem null_csp_partition : nullGraph.toCSP.partition interaction unaryWeight = 1 := by
  rw [Graph.partition_toCSP, null_partition]

/-- A zero unary resource annihilates each assignment on a nonempty vertex set. -/
theorem zero_unary_partition :
    isolatedGraph.partition interaction (fun _ => 0) = 0 := by
  simp only [Graph.partition_isolated, Finset.sum_const_zero]

theorem zero_unary_csp_partition :
    isolatedGraph.toCSP.partition interaction (fun _ => 0) = 0 := by
  rw [Graph.partition_toCSP, zero_unary_partition]

/-- A zero interaction annihilates each assignment when at least one edge occurs. -/
theorem zero_interaction_partition :
    combinedGraph.partition (fun _ _ => 0) unaryWeight = 0 := by
  simp [Graph.partition, Model.MultiGraph.partition, Model.MultiGraph.assignmentWeight,
    combinedGraph, Fin.prod_univ_succ]

theorem zero_interaction_csp_partition :
    combinedGraph.toCSP.partition (fun _ _ => 0) unaryWeight = 0 := by
  rw [Graph.partition_toCSP, zero_interaction_partition]

/-- With no vertices there is still one assignment even over the empty domain. -/
theorem null_empty_domain_partition :
    nullGraph.partition (fun x : Empty => x.elim) (fun x => x.elim) = (1 : Nat) := by
  exact Graph.partition_null _ _

theorem null_empty_domain_csp_partition :
    nullGraph.toCSP.partition (fun x : Empty => x.elim) (fun x => x.elim) = (1 : Nat) := by
  rw [Graph.partition_toCSP, null_empty_domain_partition]

/-- A nonempty vertex set has no assignment into the empty domain. -/
theorem isolated_empty_domain_partition :
    isolatedGraph.partition (fun x : Empty => x.elim) (fun x => x.elim) = (0 : Nat) := by
  simp only [Graph.partition_isolated, Fintype.sum_empty]

theorem isolated_empty_domain_csp_partition :
    isolatedGraph.toCSP.partition (fun x : Empty => x.elim) (fun x => x.elim) = (0 : Nat) := by
  rw [Graph.partition_toCSP, isolated_empty_domain_partition]

/-- A valid target with constraint order and multiplicities not required to arise
from the graph adapter. The target serializer accepts this independently. -/
abbrev arbitraryCSP : CSP := ⟨2, [.binary 1 0, .unary 1, .unary 1]⟩

theorem arbitrary_csp_roundtrip : cspDecode (cspEncode arbitraryCSP) = some arbitraryCSP :=
  cspDecode_encode arbitraryCSP

theorem arbitrary_csp_not_graph : graphOfCSP arbitraryCSP = none := by
  decide

/-- Faithfulness of the target encoding is not restricted to adapter outputs. -/
theorem arbitrary_csp_outside_image (G : Graph) : G.toCSP ≠ arbitraryCSP := by
  intro h
  have hg := graphOfCSP_toCSP G
  rw [h, arbitrary_csp_not_graph] at hg
  cases hg

theorem combined_graph_roundtrip :
    graphDecode (graphEncode combinedGraph) = some combinedGraph :=
  graphDecode_encode combinedGraph

theorem combined_transformed_roundtrip :
    cspDecode ((graphEncode combinedGraph).map symbolMap) = some combinedGraph.toCSP :=
  decode_transform combined_graph_roundtrip

/-- The example's unary header, binary vertex declarations, and binary edge
records have 24 symbols altogether. -/
theorem combined_code_length : (graphEncode combinedGraph).length = 24 := by
  decide

/-- The complete F1 reduction object includes the proved finite TM2 program. -/
noncomputable def concreteReduction :
    Counting.Complexity.ParsimoniousReduction graphEncoding cspEncoding
      (fun G => G.partition interaction unaryWeight)
      (fun I => I.partition interaction unaryWeight) :=
  graphToCSPReduction interaction unaryWeight

theorem concrete_reduction_map : concreteReduction.map combinedGraph = combinedGraph.toCSP := rfl

theorem concrete_reduction_value :
    (concreteReduction.map combinedGraph).partition interaction unaryWeight = 5298 :=
  combined_csp_partition

/-- This is the machine's actual transition count, separately from output size. -/
theorem concrete_reduction_steps :
    (concreteReduction.machine.outputsFun combinedGraph).steps = 51 := by
  change (graphTransformer.outputsFun combinedGraph).steps = 51
  rw [graphTransformer_steps, combined_code_length]

set_option backward.isDefEq.respectTransparency false in
/-- The actual TM2 reaches the concrete encoded target after 51 transitions. -/
theorem concrete_machine_run :
    (fun c : Option graphTransformer.tm.Cfg => c.bind graphTransformer.tm.step)^[51]
      (some (Turing.initList graphTransformer.tm (graphEncode combinedGraph))) =
        some (Turing.haltList graphTransformer.tm (cspEncode combinedGraph.toCSP)) := by
  have h := graphTransformer_run (graphEncode combinedGraph)
  rw [combined_code_length, encode_transform] at h
  exact h

theorem concrete_reduction_time : concreteReduction.machine.time =
    Polynomial.C 2 * Polynomial.X + Polynomial.C 3 := graphTransformer_time

end Counting.GraphCSP.Examples
