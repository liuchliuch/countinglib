import Counting.Algorithm.VariableEliminationWidth.Projection
import Counting.Algorithm.VariableEliminationWidth.Leaf
import Counting.Algorithm.VariableElimination.Order

/-! # Executable leaf peeling and its complete elimination order -/

namespace Counting.Algorithm.VariableEliminationWidth

open Counting.Algorithm.VariableElimination

/-- A trace of actual leaf operations. Its pivot premises are private membership,
not bucket-width assumptions. Dropping an absorbed leaf produces no pivot. -/
inductive Peeling : {V : Type} → [LinearOrder V] → List (Finset V) → Type 1 where
  | done {V : Type} [LinearOrder V] {bags : List (Finset V)}
      (empty : IsEmpty V) : Peeling bags
  | drop {V : Type} [LinearOrder V] (bag : Finset V) {bags : List (Finset V)}
      (parent : Fin bags.length)
      (overlap : ∀ other ∈ bags, bag ∩ other ⊆ bags.get parent)
      (empty : privateVertices bag bags = ∅) (rest : Peeling bags) : Peeling (bag :: bags)
  | step {V : Type} [LinearOrder V] (bag : Finset V) (bags : List (Finset V))
      (v : V) (hprivate : v ∈ privateVertices bag bags)
      (rest : Peeling ((bag :: bags).map (projectBag v))) : Peeling (bag :: bags)

/-- Forget bag-deletion steps and keep the actual pivots, in dependent remaining
variable types. The result is accepted directly by the established executor. -/
def Peeling.order : {V : Type} → [LinearOrder V] → {bags : List (Finset V)} →
    Peeling bags → EliminationOrder V
  | _V, _inst, _bags, @Peeling.done _ _ _ h => .done h
  | _V, _inst, _, @Peeling.drop _ _ _ _ _ _ _ rest => rest.order
  | _V, _inst, _, @Peeling.step _ _ _ _ v _ rest => .step v rest.order

/-- Construct a complete order from a supplied bag tree. Each recursive call
strictly decreases the number of variables plus the number of bags. -/
def peel {V : Type} [Fintype V] [LinearOrder V] {width : Nat}
    (d : Decomposition V width) : Peeling d.bags :=
  match d with
  | ⟨_, .root bag, cover, bound⟩ =>
      match h : bag.sort (· ≤ ·) with
      | [] => .done ⟨fun v => by
          obtain ⟨b, hb, hv⟩ := cover v
          have heq : b = bag := by simpa using hb
          subst b
          have : v ∈ bag.sort (· ≤ ·) := by simpa using hv
          simp [h] at this⟩
      | v :: vs =>
          .step bag [] v (by
            apply (mem_privateVertices v bag []).mpr
            constructor
            · have : v ∈ bag.sort (· ≤ ·) := by simp [h]
              simpa using this
            · simp)
            (peel ((Decomposition.mk [bag] (.root bag) cover bound).project v))
  | ⟨_, @BagTree.attach _ _ bag bags rest parent overlap, cover, bound⟩ =>
      match h : (privateVertices bag bags).sort (· ≤ ·) with
      | [] => .drop bag parent overlap (by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          have : x ∈ (privateVertices bag bags).sort (· ≤ ·) := by simpa using hx
          simp [h] at this)
          (peel (dropLeaf bag bags rest parent overlap cover bound (by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          have : x ∈ (privateVertices bag bags).sort (· ≤ ·) := by simpa using hx
          simp [h] at this)))
      | v :: vs => .step bag bags v (by
          have : v ∈ (privateVertices bag bags).sort (· ≤ ·) := by simp [h]
          simpa using this)
          (peel ((Decomposition.mk _ (.attach bag rest parent overlap) cover bound).project v))
termination_by Fintype.card V + d.bags.length
  decreasing_by
    all_goals simp only [Decomposition.project, dropLeaf, List.length_map, List.length_cons]
    · have hlt : Fintype.card (Remaining v) < Fintype.card V :=
        Fintype.card_subtype_lt (p := fun x => x ≠ v) (x := v) (by simp)
      omega
    · omega
    · have hlt : Fintype.card (Remaining v) < Fintype.card V :=
        Fintype.card_subtype_lt (p := fun x => x ≠ v) (x := v) (by simp)
      omega

/-- The order is computed only from bags and their parent certificates; factors
and their values play no role in choosing its pivots. -/
def Decomposition.order {V : Type} [Fintype V] [LinearOrder V] {width : Nat}
    (d : Decomposition V width) : EliminationOrder V := (peel d).order

end Counting.Algorithm.VariableEliminationWidth
