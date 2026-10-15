import Counting.Algorithm.VariableEliminationWidth.Peeling

/-! # Dynamic scope bounds for the constructed order -/

namespace Counting.Algorithm.VariableEliminationWidth

open Counting.Algorithm.VariableElimination

variable {D R : Type} [Fintype D] [LinearOrder D] [CommSemiring R]

/-- A property of the executable trajectory: at each step use the actual current
factors and then the materialized `eliminate` result. This is a conclusion of the
bag-tree construction, not a field of its supplied input certificate. -/
def ScopeBound (width : Nat) : {V : Type} → [Fintype V] → [LinearOrder V] →
    EliminationOrder V → List (Factor V D R) → Prop
  | _, _, _, .done _, _ => True
  | _, _, _, .step v rest, fs =>
      (bucketVars v fs).length ≤ width ∧ ScopeBound width rest (eliminate v fs)

/-- Every private-vertex peeling trace bounds the actual dynamic buckets. -/
theorem Peeling.scopeBound {V : Type} [finV : Fintype V] [LinearOrder V]
    {bags : List (Finset V)} (p : Peeling bags) (width : Nat)
    (bound : ∀ bag ∈ bags, bag.card ≤ width + 1)
    (fs : List (Factor V D R)) (covered : Bagged bags fs) :
    ScopeBound width p.order fs := by
  induction p generalizing finV with
  | done h => trivial
  | @drop V inst bag bags parent overlap empty rest ih =>
      exact ih (fun b hb => bound b (List.mem_cons_of_mem _ hb)) fs
        (bagged_dropLeaf bag bags parent overlap empty fs covered)
  | @step V inst bag bags v hprivate rest ih =>
      constructor
      · exact bucketVars_length_le bag bags fs covered v hprivate width (bound bag (by simp))
      · apply ih _ (eliminate v fs) (bagged_eliminate bag bags fs covered v hprivate)
        intro b hb
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hb
        exact (card_projectBag_le v old).trans (bound old hold)

/-- Supplied input bags produce a complete elimination order whose induced
bucket scopes satisfy the supplied width bound, for every bag-covered factor list. -/
theorem Decomposition.scopeBound {V : Type} [Fintype V] [LinearOrder V]
    {width : Nat} (d : Decomposition V width) (fs : List (Factor V D R))
    (covered : Bagged d.bags fs) : ScopeBound width d.order fs :=
  (peel d).scopeBound width d.card_le fs covered

/-- Evaluation under the order constructed from bags retains the full finite
partition semantics, including isolated variables and empty colour domains. -/
theorem Decomposition.evaluate_eq_partition {V : Type} [Fintype V] [LinearOrder V]
    {width : Nat} (d : Decomposition V width) (fs : List (Factor V D R)) :
    d.order.evaluate fs = partition fs := EliminationOrder.evaluate_eq_partition _ _

end Counting.Algorithm.VariableEliminationWidth
