import Counting.Algorithm.VariableElimination.Bridge
import Counting.Algorithm.VariableElimination.MeasuredOrder
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum

/-!
# Executable regression examples

The sparse example has two disconnected components, one repeated occurrence,
one nullary occurrence, and one isolated variable. Its first bucket touches only
two occurrences. The pinned example additionally has repeated hidden ports.
All theorem and example declarations below are checked by the kernel. The
`#eval` commands additionally exercise code generation and assert the concrete
whole-run traces for the actual materializing executor.
-/

namespace Counting.Algorithm.VariableElimination.Examples

/-- A nullary factor of arbitrary weight. -/
def scalarFactor {V D R : Type} (r : R) : Factor V D R :=
  ⟨0, Fin.elim0, fun _ => r⟩

/-- A two-colour interaction with weight two for equal endpoints. -/
def pairFactor {R : Type} [CommSemiring R] (v w : Fin 5) : Factor (Fin 5) (Fin 2) R where
  arity := 2
  scope := fun i => if i = 0 then v else w
  value := fun x => if x 0 = x 1 then 2 else 1

/-- Components 0--1 and 2--3, with variable 4 explicitly isolated. -/
def sparseNatural : List (Factor (Fin 5) (Fin 2) Nat) :=
  [pairFactor 0 1, pairFactor 0 1, pairFactor 2 3, scalarFactor 3]

/-- The same scope structure with a rational nullary weight. -/
def sparseRational : List (Factor (Fin 5) (Fin 2) ℚ) :=
  [pairFactor 0 1, pairFactor 0 1, pairFactor 2 3, scalarFactor (3 / 2)]

theorem sparse_first_bucket : (bucket 0 sparseNatural).length = 2 := by decide
theorem sparse_first_outside : (outside 0 sparseNatural).length = 2 := by decide
theorem sparse_first_scope : (bucketVars 0 sparseNatural).length = 1 := by
  simp only [bucketVars, Finset.length_sort]
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem sparseNatural_run : EliminationOrder.run sparseNatural = 360 := by
  rw [EliminationOrder.run_eq_partition]
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem sparseRational_run : EliminationOrder.run sparseRational = 180 := by
  have hw (a : Fin 5 → Fin 2) :
      weight sparseRational a = ((weight sparseNatural a : Nat) : ℚ) / 2 := by
    simp only [weight, sparseRational, sparseNatural, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, Factor.eval, pairFactor, scalarFactor,
      Function.comp_apply]
    split_ifs <;> norm_num
  rw [EliminationOrder.run_eq_partition]
  calc
    partition sparseRational = ((partition sparseNatural : Nat) : ℚ) / 2 := by
      simp only [partition, hw, div_eq_mul_inv, Finset.sum_mul, Nat.cast_sum]
    _ = 180 := by
      rw [← EliminationOrder.run_eq_partition, sparseNatural_run]
      norm_num

#eval EliminationOrder.run sparseNatural
#eval EliminationOrder.run sparseRational

/-- A supplied order can start with an isolated variable instead of the least one. -/
def isolatedFirst : EliminationOrder (Fin 5) :=
  .step 4 (EliminationOrder.canonical (Remaining (4 : Fin 5)))

theorem isolatedFirst_run : isolatedFirst.evaluate sparseNatural = 360 := by
  rw [EliminationOrder.evaluate_eq_partition,
    ← EliminationOrder.run_eq_partition, sparseNatural_run]

#eval isolatedFirst.evaluate sparseNatural

/-- A language whose first symbol has one boundary port and two repeated hidden
ports, and whose second symbol is nullary. -/
def pinnedLanguage : Model.Language (Fin 2) Nat (Fin 2) where
  arity := fun i => if i = 0 then 3 else 0
  value := fun i x => if h : i = 0 then
    if x ⟨0, by simp [h]⟩ = x ⟨1, by simp [h]⟩ then
      if x ⟨1, by simp [h]⟩ = x ⟨2, by simp [h]⟩ then 2 else 17
    else 1
    else 3

def pinnedOccurrence : Model.Occurrence pinnedLanguage (Fin 1 ⊕ Fin 2) where
  symbol := 0
  scope := fun i => if i.val = 0 then .inl 0 else .inr 0

def pinnedNullary : Model.Occurrence pinnedLanguage (Fin 1 ⊕ Fin 2) where
  symbol := 1
  scope := fun i => Fin.elim0 (show Fin 0 from i)

/-- The second hidden variable is isolated. Both nonnullary occurrences and the
repeated hidden port within each occurrence are intentionally retained. -/
def pinnedInstance : Model.OpenInstance pinnedLanguage (Fin 1) (Fin 2) :=
  ⟨[pinnedOccurrence, pinnedOccurrence, pinnedNullary]⟩

example : (pinOccurrence (fun _ => 0) pinnedOccurrence).arity = 2 := by decide
example : (pinnedFactors pinnedInstance (fun _ => 0)).length = 3 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem pinned_run :
    EliminationOrder.run (pinnedFactors pinnedInstance (fun _ => 0)) = 30 := by
  rw [run_pinnedFactors]
  decide

#eval EliminationOrder.run (pinnedFactors pinnedInstance (fun _ => 0))

/-- A repeated scope evaluates the diagonal tuple, not independent port colours. -/
def repeatedScope : Factor (Fin 1) (Fin 2) Nat where
  arity := 2
  scope := fun _ => 0
  value := fun x => if x 0 = x 1 then 2 else 17

set_option maxRecDepth 10000 in
example : EliminationOrder.run [repeatedScope] = 4 := by
  rw [EliminationOrder.run_eq_partition]
  decide

set_option maxRecDepth 10000 in
example : EliminationOrder.run ([] : List (Factor (Fin 1) (Fin 0) Nat)) = 0 := by
  rw [EliminationOrder.run_eq_partition]
  decide

set_option maxRecDepth 10000 in
example : EliminationOrder.run ([] : List (Factor (Fin 0) (Fin 0) Nat)) = 1 := by
  rw [EliminationOrder.run_eq_partition]
  decide

set_option maxRecDepth 10000 in
example : EliminationOrder.run ([scalarFactor 3] : List (Factor (Fin 0) (Fin 0) Nat)) = 3 := by
  rw [EliminationOrder.run_eq_partition]
  decide

set_option maxRecDepth 10000 in
example : EliminationOrder.run ([scalarFactor 0] : List (Factor (Fin 2) (Fin 2) Nat)) = 0 := by
  rw [EliminationOrder.run_eq_partition]
  decide

theorem sparse_measured_value : (EliminationOrder.runMeasured sparseNatural).value = 360 := by
  rw [EliminationOrder.value_runMeasured, sparseNatural_run]

theorem sparse_first_additions : (eliminateMeasured 0 sparseNatural).additions = 4 := by
  simp [sparse_first_scope]

theorem sparse_first_multiplications :
    (eliminateMeasured 0 sparseNatural).multiplications = 8 := by
  simp [sparse_first_scope, sparse_first_bucket]

theorem sparse_first_table_rows :
    (DenseTable.tabulateMeasured (measuredBucketRow 0 sparseNatural)).value.rowCount = 2 := by
  simp [sparse_first_scope]

example : (enumerateAssignments (Fin 5) (Fin 2)).length = 32 := by simp

/-- The same instance supplied explicitly as stored dense input arrays. -/
def tabulatedSparse : List (TabulatedFactor (Fin 5) (Fin 2) Nat) :=
  sparseNatural.map TabulatedFactor.tabulate

def storedSparse : List (Factor (Fin 5) (Fin 2) Nat) :=
  tabulatedSparse.map TabulatedFactor.toFactor

@[simp] theorem storedSparse_eq : storedSparse = sparseNatural := by
  simp [storedSparse, tabulatedSparse, List.map_map, Function.comp_def]

theorem storedSparse_measured_value :
    (EliminationOrder.runMeasured storedSparse).value = 360 := by
  rw [storedSparse_eq, sparse_measured_value]

#eval let result := EliminationOrder.runMeasured storedSparse
  (result.value, result.additions, result.multiplications)
#eval let result := EliminationOrder.runMeasured sparseNatural
  (result.value, result.additions, result.multiplications)
#eval (EliminationOrder.canonical (Fin 5)).scopeTrace sparseNatural
#eval (EliminationOrder.canonical (Fin 5)).tableRowTrace sparseNatural
#eval (EliminationOrder.canonical (Fin 5)).endpointFactorCount sparseNatural

/- Regression assertions for generated code. The general correctness and exact
count formulas are kernel theorems; these concrete whole-run traces are runtime
checks, separate from the kernel value and first-step equalities above. -/
#eval do
  let result := EliminationOrder.runMeasured sparseNatural
  let stored := EliminationOrder.runMeasured storedSparse
  unless (result.value, result.additions, result.multiplications) = (360, 14, 20) do
    throw (IO.userError "Unexpected sparse measured result")
  unless (stored.value, stored.additions, stored.multiplications) = (360, 14, 20) do
    throw (IO.userError "Unexpected explicitly tabulated input result")
  unless (EliminationOrder.canonical (Fin 5)).scopeTrace sparseNatural =
      [(1, 2), (0, 1), (1, 1), (0, 1), (0, 0)] do
    throw (IO.userError "Unexpected induced scope trace")
  unless (EliminationOrder.canonical (Fin 5)).tableRowTrace sparseNatural = [2, 1, 2, 1, 1] do
    throw (IO.userError "Unexpected materialized table sizes")
  unless (EliminationOrder.canonical (Fin 5)).endpointFactorCount sparseNatural = 4 do
    throw (IO.userError "Unexpected final scalar-factor count")
  unless EliminationOrder.run sparseRational = 180 do
    throw (IO.userError "Unexpected rational result")
  unless isolatedFirst.evaluate sparseNatural = 360 do
    throw (IO.userError "Unexpected supplied-order result")
  unless EliminationOrder.run (pinnedFactors pinnedInstance (fun _ => 0)) = 30 do
    throw (IO.userError "Unexpected pinned instance result")
  IO.println "All executable regression assertions passed."

end Counting.Algorithm.VariableElimination.Examples
