import Counting.Algorithm.CPOG.CNF
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Concrete occurrence-sensitive CNFs and normalized signed-weight clients. -/
namespace Counting.Algorithm.CPOG.CNF.Clients
open scoped BigOperators

def positiveZero : Literal 2 := ⟨0, true⟩
def negativeZero : Literal 2 := ⟨0, false⟩
def negativeOne : Literal 2 := ⟨1, false⟩

/-- Both clause occurrences and both repeated literal ports are retained. -/
def repeated : Formula 2 := [[positiveZero, positiveZero], [positiveZero, positiveZero]]
def tautology : Formula 2 := [[positiveZero, negativeZero, positiveZero]]
def contradiction : Formula 2 := [[positiveZero], [negativeZero]]
def ordered : Formula 2 := [[positiveZero, negativeOne]]

theorem repeated_eval (a : Fin 2 → Bool) : Formula.eval repeated a = a 0 := by
  simp [Formula.eval, Clause.eval, Literal.eval, Literal.apply, repeated, positiveZero]

theorem tautology_eval (a : Fin 2 → Bool) : Formula.eval tautology a = true := by
  cases h : a 0 <;>
    simp [Formula.eval, Clause.eval, Literal.eval, Literal.apply, tautology, positiveZero, negativeZero, h]

theorem contradiction_eval (a : Fin 2 → Bool) : Formula.eval contradiction a = false := by
  cases h : a 0 <;>
    simp [Formula.eval, Clause.eval, Literal.eval, Literal.apply, contradiction, positiveZero, negativeZero, h]

theorem repeated_occurrences : (Formula.toInstance repeated).occurrences.length = 2 := rfl

theorem repeated_ports :
    (Formula.occurrence ℕ repeated ⟨0, by decide⟩).scope ⟨0, by decide⟩ = Sum.inr 0 ∧
    (Formula.occurrence ℕ repeated ⟨0, by decide⟩).scope ⟨1, by decide⟩ = Sum.inr 0 := ⟨rfl, rfl⟩

theorem ordered_ports :
    (Formula.occurrence ℕ ordered ⟨0, by decide⟩).scope ⟨0, by decide⟩ = Sum.inr 0 ∧
    (Formula.occurrence ℕ ordered ⟨0, by decide⟩).scope ⟨1, by decide⟩ = Sum.inr 1 := ⟨rfl, rfl⟩

theorem weighted_occurrences {R : Type} [CommRing R] (w : Fin 2 → R) :
    (Formula.weightedInstance repeated w).occurrences.length = 4 := rfl

/-- Enumerate all assignments, including the second variable absent from clauses. -/
theorem sum_assignments_two {R : Type} [AddCommMonoid R] (f : (Fin 2 → Bool) → R) :
    (∑ a : Fin 2 → Bool, f a) =
      f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp f, Fintype.sum_prod_type]
  simp [add_assoc, add_comm]

/-- The isolated variable contributes two assignments in unweighted counting. -/
theorem repeated_partition : (Formula.toInstance repeated).partition Empty.elim = 2 := by
  rw [Formula.partition_eq_sum, sum_assignments_two]
  simp [repeated_eval]

theorem tautology_partition : (Formula.toInstance tautology).partition Empty.elim = 4 := by
  rw [Formula.partition_eq_sum]
  simp [tautology_eval]

theorem contradiction_partition : (Formula.toInstance contradiction).partition Empty.elim = 0 := by
  rw [Formula.partition_eq_sum]
  simp [contradiction_eval]

/-- Complementary weights cancel the isolated variable's contribution to one. -/
theorem repeated_weighted {R : Type} [CommRing R] (w : Fin 2 → R) :
    (Formula.weightedInstance repeated w).partition Empty.elim = w 0 := by
  rw [Formula.weighted_partition_eq_sum, sum_assignments_two]
  simp [repeated_eval, Fin.prod_univ_two]
  ring

def signedWeights : Fin 2 → ℚ := ![-2, 3]

/-- Normalization does not imply nonnegative weights or a probability measure. -/
theorem signed_weights_normalized (i : Fin 2) : signedWeights i + (1 - signedWeights i) = 1 := by
  ring

theorem negative_weighted_count :
    (Formula.weightedInstance repeated signedWeights).partition Empty.elim = -2 := by
  rw [repeated_weighted]
  rfl

theorem signed_empty_formula :
    (Formula.weightedInstance ([] : Formula 2) signedWeights).partition Empty.elim = 1 :=
  Formula.weighted_partition_empty signedWeights

theorem empty_clause :
    (Formula.toInstance ([[]] : Formula 2)).partition Empty.elim = 0 :=
  Formula.partition_empty_clause []

theorem signed_empty_clause :
    (Formula.weightedInstance ([[]] : Formula 2) signedWeights).partition Empty.elim = 0 :=
  Formula.weighted_partition_empty_clause [] signedWeights

/-- There is one assignment on no variables, even for the empty formula. -/
theorem zero_variables_empty : (Formula.toInstance ([] : Formula 0)).partition Empty.elim = 1 := by
  simpa using (Formula.partition_empty (n := 0))

/-- A nullary empty clause is false on that unique empty assignment. -/
theorem zero_variables_empty_clause :
    (Formula.toInstance ([[]] : Formula 0)).partition Empty.elim = 0 :=
  Formula.partition_empty_clause []

theorem zero_variables_weighted {R : Type} [CommRing R] :
    (Formula.weightedInstance ([] : Formula 0) (fun i => Fin.elim0 i : Fin 0 → R)).partition
      Empty.elim = 1 := Formula.weighted_partition_empty _

end Counting.Algorithm.CPOG.CNF.Clients
