import Counting.Algorithm.VariableElimination.Program
import Mathlib.Data.Fintype.Card

/-!
# Supplied elimination orders

An order removes one variable at each step, and carries an empty-type certificate
at its endpoint. Consequently every supplied order is complete and cannot select
a variable twice. The evaluator executes the bucket program at every step and
finishes by multiplying the remaining nullary factors.
-/

namespace Counting.Algorithm.VariableElimination

/-- A complete dependent elimination order. The next choice is made in the type
of remaining variables, so removed variables cannot be selected again. -/
inductive EliminationOrder : Type → Type 1 where
  | done {V : Type} (empty : IsEmpty V) : EliminationOrder V
  | step {V : Type} (v : V) (rest : EliminationOrder (Remaining v)) : EliminationOrder V

namespace EliminationOrder

variable {V D R : Type}

/-- The number of actual elimination steps in the supplied order. -/
def length : {V : Type} → EliminationOrder V → Nat
  | _, .done _ => 0
  | _, .step _ rest => rest.length + 1

/-- Every complete order has one step per variable, including isolated variables. -/
theorem length_eq_card {V : Type} [finV : Fintype V] [decV : DecidableEq V]
    (order : EliminationOrder V) : order.length = Fintype.card V := by
  induction order generalizing finV decV with
  | done h =>
    let := h
    simp [length]
  | @step V v rest ih =>
    have hcard : Fintype.card (Remaining v) = Fintype.card V - 1 := by
      simp [Remaining, Fintype.card_subtype_compl]
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    simp only [length, ih]
    omega

/-- The ascending order of the current variable type, constructed executably by
sorting its finite enumeration and recursing on the strictly smaller type. -/
def canonical (V : Type) [Fintype V] [LinearOrder V] : EliminationOrder V :=
  match h : (Finset.univ : Finset V).sort (· ≤ ·) with
  | [] => .done ⟨fun v => by
      have hv : v ∈ (Finset.univ : Finset V).sort (· ≤ ·) := by simp
      simp [h] at hv⟩
  | v :: _ => .step v (canonical (Remaining v))
termination_by Fintype.card V
  decreasing_by exact Fintype.card_subtype_lt (x := v) (by simp)

/-- Execute one materialized bucket transformation per supplied variable. The
empty endpoint evaluates its unique assignment, without enumerating assignments. -/
def evaluate [CommSemiring R] [Fintype D] [LinearOrder D] :
    {V : Type} → [Fintype V] → [LinearOrder V] →
      EliminationOrder V → List (Factor V D R) → R
  | _, _, _, .done h, fs => weight fs (fun v => (h.false v).elim)
  | _, _, _, .step v rest, fs => rest.evaluate (eliminate v fs)

/-- The state invariant transported through all elimination steps. -/
theorem evaluate_eq_partition [CommSemiring R] [Fintype D] [LinearOrder D]
    {V : Type} [finV : Fintype V] [ordV : LinearOrder V] (order : EliminationOrder V)
    (fs : List (Factor V D R)) : order.evaluate fs = partition fs := by
  induction order generalizing finV ordV with
  | done h =>
    let := h
    simp only [evaluate, partition, Fintype.sum_unique]
    exact congrArg (weight fs) (Subsingleton.elim _ _)
  | step v rest ih =>
    rw [evaluate, ih]
    exact partition_eliminate v fs

/-- The canonical executable evaluator is correct for arbitrary finite variables,
domains, and commutative semiring values. -/
def run [CommSemiring R] [Fintype D] [LinearOrder D] [Fintype V] [LinearOrder V]
    (fs : List (Factor V D R)) : R := (canonical V).evaluate fs

@[simp] theorem run_eq_partition [CommSemiring R] [Fintype D] [LinearOrder D]
    [Fintype V] [LinearOrder V] (fs : List (Factor V D R)) :
    run fs = partition fs := evaluate_eq_partition _ _

/-- Every supplied order returns the same result. -/
theorem evaluate_order_independent [CommSemiring R] [Fintype D] [LinearOrder D]
    [Fintype V] [LinearOrder V] (first second : EliminationOrder V)
    (fs : List (Factor V D R)) : first.evaluate fs = second.evaluate fs := by
  rw [evaluate_eq_partition, evaluate_eq_partition]

end EliminationOrder
end Counting.Algorithm.VariableElimination
