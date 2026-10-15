import Counting.GraphCSP.Reduction

/-! A real parsimonious reduction with fixed natural weights. The graph has a
loop, two parallel ordered edges, and an isolated vertex. The machine transforms
the complete serialized instance; its cost is measured in source symbols. -/

noncomputable section

namespace Counting.Tutorial.GraphToCSP

open Counting.GraphCSP
open scoped BigOperators

def interaction (x y : Bool) : Nat :=
  if x then (if y then 7 else 5) else (if y then 3 else 2)

def vertexWeight (x : Bool) : Nat := if x then 2 else 1

abbrev graph : Graph := ⟨3, [(0, 0), (0, 1), (0, 1)]⟩

theorem constraints_preserved : graph.toCSP.constraints =
    (show List (Constraint 3) from
      [.unary 0, .unary 1, .unary 2, .binary 0 0, .binary 0 1, .binary 0 1]) := rfl

-- Match the equality instance used by the partition semantics.
local instance (n : Nat) : DecidableEq (Fin n) := fun _ _ => Classical.propDecidable _

private theorem sum_boolean_assignments (n : Nat) (f : (Fin (n + 1) → Bool) → Nat) :
    (∑ a, f a) = ∑ x : Bool, ∑ a : Fin n → Bool, f (Fin.cons x a) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp f,
    Fintype.sum_prod_type]
  rfl

theorem graph_value : graph.partition interaction vertexWeight = 5298 := by
  unfold Graph.partition Counting.Model.MultiGraph.partition
  change (∑ a : Fin 3 → Bool,
    graph.toMultiGraph.assignmentWeight interaction (fun _ => vertexWeight) a) = 5298
  simp only [sum_boolean_assignments, Fintype.sum_bool]
  simp [Counting.Model.MultiGraph.assignmentWeight, Graph.toMultiGraph, graph,
    Fin.prod_univ_succ, interaction, vertexWeight]

def reduction : Counting.Complexity.ParsimoniousReduction graphEncoding cspEncoding
    (fun G => G.partition interaction vertexWeight)
    (fun I => I.partition interaction vertexWeight) :=
  graphToCSPReduction interaction vertexWeight

theorem target_value :
    (reduction.map graph).partition interaction vertexWeight = 5298 := by
  change graph.toCSP.partition interaction vertexWeight = 5298
  rw [Graph.partition_toCSP, graph_value]

theorem machine_steps : (reduction.machine.outputsFun graph).steps = 51 := by
  change (graphTransformer.outputsFun graph).steps = 51
  rw [graphTransformer_steps]
  have h : (graphEncode graph).length = 24 := by decide
  rw [h]

end Counting.Tutorial.GraphToCSP
