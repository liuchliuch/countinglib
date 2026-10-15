import Counting.Algorithm.Product.Input
import Holant.Proofs.Tractability.ProductEliminationBounds

/-!
# Executable product elimination and its public semantic bridge

The existing Holant elimination is the sole backend. Compilation translates
public S1 labels/scopes into its factors; it does not deduplicate occurrences or
remove unused variables. Arithmetic-operation and factor-visit costs are kept
separate from bit-machine transition counts.
-/

namespace Counting.Algorithm.Product

open Holant.LocalDrafts.Tractability

variable {K : Type} [CommSemiring K] {n : Nat}

/-- Compile the actual ordered scope into the existing elimination language. -/
def compileOccurrence (c : Occurrence K n) : ProductElimination.Factor K n :=
  match c.symbol, c.scope with
  | .scalar a, _ => .scalar a
  | .unary f t, scope => .unary (scope (0 : Fin 1)) (fun b => if b then t else f)
  | .equality, scope => .link (scope (0 : Fin 2)) (scope (1 : Fin 2)) false
  | .disequality, scope => .link (scope (0 : Fin 2)) (scope (1 : Fin 2)) true

/-- Compilation preserves the value of each occurrence, even for repeated ports. -/
theorem compileOccurrence_eval (c : Occurrence K n) (x : Fin n → Bool) :
    (compileOccurrence c).eval x = c.eval x := by
  rcases c with ⟨s, scope⟩
  cases s with
  | scalar a => rfl
  | unary f t => rfl
  | equality =>
    change (if x (scope (0 : Fin 2)) = Bool.xor (x (scope (1 : Fin 2))) false then (1 : K) else 0) =
      (if x (scope (0 : Fin 2)) = x (scope (1 : Fin 2)) then 1 else 0)
    cases x (scope (0 : Fin 2)) <;> cases x (scope (1 : Fin 2)) <;> rfl
  | disequality =>
    change (if x (scope (0 : Fin 2)) = Bool.xor (x (scope (1 : Fin 2))) true then (1 : K) else 0) =
      (if x (scope (0 : Fin 2)) ≠ x (scope (1 : Fin 2)) then 1 else 0)
    cases x (scope (0 : Fin 2)) <;> cases x (scope (1 : Fin 2)) <;> rfl

/-- One backend factor per public occurrence. -/
def Instance.compile (I : Instance K) : List (ProductElimination.Factor K I.variableCount) :=
  I.occurrences.map compileOccurrence

@[simp] theorem Instance.compile_length (I : Instance K) :
    I.compile.length = I.factorCount := by simp [compile, factorCount]

/-- Assignment weights agree before taking any sums. -/
theorem Instance.compile_weight (I : Instance K) (x : Fin I.variableCount → Bool) :
    ProductElimination.weight I.compile x = I.toOpenInstance.eval Empty.elim x := by
  simp [ProductElimination.weight, compile, toOpenInstance, Model.OpenInstance.eval,
    List.map_map, Function.comp_def, compileOccurrence_eval, Model.Occurrence.eval,
    Model.Occurrence.rename]

/-- The backend sum equals the public S1 partition, including isolated variables. -/
theorem Instance.compile_partition (I : Instance K) :
    ProductElimination.partition I.compile = I.partition := by
  unfold ProductElimination.partition Instance.partition Model.OpenInstance.partition
  apply Finset.sum_congr rfl
  intro x _
  exact I.compile_weight x

/-- The existing single-recursion elimination applied to the compiled input. -/
def evaluate (I : Instance K) : K := ProductElimination.evaluate I.compile

/-- The actual executable, annotated by coefficient additions/multiplications. -/
def run (I : Instance K) : K × Nat := ProductElimination.run I.compile

/-- Syntactic factor visits charged by the existing scan/rewrite recurrence. -/
def factorVisits (I : Instance K) : Nat := ProductElimination.factorVisits I.compile

theorem evaluate_eq_partition (I : Instance K) : evaluate I = I.partition := by
  exact (ProductElimination.evaluate_eq_partition I.compile).trans I.compile_partition

theorem run_value (I : Instance K) : (run I).1 = evaluate I :=
  ProductElimination.run_value I.compile

theorem run_eq_partition (I : Instance K) : (run I).1 = I.partition :=
  (ProductElimination.run_exact I.compile).trans I.compile_partition

/-- This counts arithmetic inside elimination. It does not charge bit lengths,
input compilation, or finite-address operations as coefficient arithmetic. -/
theorem run_operations_le (I : Instance K) :
    (run I).2 ≤ (2 * I.variableCount + 1) * I.factorCount + 2 * I.variableCount := by
  simpa only [run, Instance.compile_length] using ProductElimination.run_operations_le I.compile

/-- The backend's scan/rewrite visit charge; not a bound on machine transitions. -/
theorem factorVisits_le (I : Instance K) :
    factorVisits I ≤ (2 * I.variableCount + 1) * I.factorCount := by
  simpa only [factorVisits, Instance.compile_length] using ProductElimination.factorVisits_le I.compile

/-- Simultaneous semantic correctness and arithmetic bound for the same run. -/
theorem run_correct_and_bounded (I : Instance K) :
    (run I).1 = I.toOpenInstance.partition Empty.elim ∧
      (run I).2 ≤ (2 * I.variableCount + 1) * I.factorCount + 2 * I.variableCount :=
  ⟨run_eq_partition I, run_operations_le I⟩

end Counting.Algorithm.Product
