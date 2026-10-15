import Counting.Integration.RelationalCounting

/-! A unary relation fixes one Boolean variable. The second variable is isolated,
so the instance has two satisfying assignments. Repeating the relation does not
create an additional witness choice. These are finite-counting equalities. -/

namespace Counting.Tutorial.RelationalCounting

open Counting.Model Counting.Integration
open scoped BigOperators

def relations : RelationLanguage Bool Unit where
  arity _ := 1
  holds _ a := a 0

def pin : Occurrence relations.indicator (Empty ⊕ Fin 2) :=
  ⟨(), fun _ => Sum.inr 0⟩

def problem : OpenInstance relations.indicator Empty (Fin 2) := ⟨[pin, pin]⟩

theorem duplicate_preserves_count : problem.partition Empty.elim =
    (OpenInstance.mk [pin] : OpenInstance relations.indicator Empty (Fin 2)).partition
      Empty.elim :=
  relations.partition_duplicate pin [] Empty.elim

theorem partition_is_witness_count : problem.partition Empty.elim =
    Counting.Foundation.witnessCount 2 (relations.acceptsBits problem Empty.elim) :=
  relations.partition_eq_witnessCount 2 problem Empty.elim

private theorem sum_boolean_assignments (n : Nat) (f : (Fin (n + 1) → Bool) → Nat) :
    (∑ a, f a) = ∑ x : Bool, ∑ a : Fin n → Bool, f (Fin.cons x a) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp f,
    Fintype.sum_prod_type]
  rfl

theorem two_satisfying_assignments : problem.partition Empty.elim = 2 := by
  have accepts_first (a : Fin 2 → Bool) : relations.accepts problem Empty.elim a = a 0 := by
    change (a 0 && (a 0 && true)) = a 0
    cases a 0 <;> rfl
  rw [relations.partition_eq_countAccepted]
  unfold Counting.Foundation.countAccepted
  simp only [accepts_first, sum_boolean_assignments, Fintype.sum_bool]
  simp

end Counting.Tutorial.RelationalCounting
