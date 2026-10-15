import Counting.Algorithm.Interpolation.Algorithm

/-! Ordinary Lagrange recovery on a runtime table of paired nodes and samples.
The table is not a shifted-moment table. Zero nodes are permitted. -/
namespace Counting.Algorithm.InterpolationMachine.Materialized
open scoped BigOperators
variable {K : Type} [Field K] [DecidableEq K]

abbrev Table (K : Type) := List (K × K)

/-- Retain all differently keyed nodes in their original table order. -/
def otherNodes (node : K) (table : Table K) : List K :=
  (table.map Prod.fst).filter (fun x => decide (x ≠ node))

/-- The ordinary denominator has no extra factor equal to the node. -/
def denominator (p : K × List K) : K :=
  (p.2.map (fun x => p.1 - x)).prod

def rowTerm (table : Table K) (row : K × K) : K :=
  row.2 / denominator (row.1, otherNodes row.1 table)

/-- A total list program; semantic recovery requires distinct keys. -/
def recover (table : Table K) : K := (table.map (rowTerm table)).sum

/-- The input carries precisely one paired sample for every indexed node. -/
def tableOf {n : ℕ} (nodes values : Fin n → K) : Table K :=
  List.ofFn (fun i => (nodes i, values i))

omit [Field K] [DecidableEq K] in
theorem tableOf_length {n : ℕ} (nodes values : Fin n → K) :
    (tableOf nodes values).length = n := by simp [tableOf]

/-- The list-product identity specializes the source's filtered-product proof;
only mathlib list/finite-product facts are needed in this semantic entry. -/
theorem denominator_tableOf {m : ℕ} (nodes values : Fin (m + 1) → K)
    (hi : Function.Injective nodes) (j : Fin (m + 1)) :
    denominator (nodes j, otherNodes (nodes j) (tableOf nodes values)) =
      Interpolation.interpolationDenominator nodes j := by
  change (((List.ofFn (fun i => (nodes i, values i))).map Prod.fst |>.filter
    (fun x => decide (x ≠ nodes j))).map (fun x => nodes j - x)).prod = _
  simp only [List.map_ofFn, Function.comp_def]
  have hp := List.prod_map_ite (fun x => x ≠ nodes j)
    (fun x => nodes j - x) (fun _ => (1 : K)) (List.ofFn nodes)
  simp only [List.map_const', List.prod_replicate, one_pow, mul_one] at hp
  rw [← hp, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply, ne_eq, hi.eq_iff]
  rw [← Finset.prod_filter, Finset.filter_ne']
  rfl

theorem denominator_ne_zero {m : ℕ} (nodes values : Fin (m + 1) → K)
    (hi : Function.Injective nodes) (j : Fin (m + 1)) :
    denominator (nodes j, otherNodes (nodes j) (tableOf nodes values)) ≠ 0 := by
  rw [denominator_tableOf nodes values hi j]
  exact Interpolation.interpolationDenominator_ne_zero nodes hi j

theorem recover_eq_recoverTop {m : ℕ} (nodes values : Fin (m + 1) → K)
    (hi : Function.Injective nodes) :
    recover (tableOf nodes values) = Interpolation.recoverTop nodes values := by
  change ((List.ofFn (fun i => (nodes i, values i))).map
    (rowTerm (tableOf nodes values))).sum = _
  rw [List.map_ofFn, List.sum_ofFn]
  change (∑ i, values i / denominator
    (nodes i, otherNodes (nodes i) (tableOf nodes values))) = _
  simp only [denominator_tableOf nodes values hi]
  rfl

theorem recover_eq_evaluate {m : ℕ} (nodes values : Fin (m + 1) → K)
    (hi : Function.Injective nodes) :
    recover (tableOf nodes values) = Interpolation.evaluate nodes values := by
  rw [Interpolation.evaluate_eq_recoverTop, recover_eq_recoverTop nodes values hi]

theorem recover_eq_coefficient {m : ℕ} (nodes : Fin (m + 1) → K)
    (hi : Function.Injective nodes) (P : Polynomial K) (hP : P.natDegree ≤ m) :
    recover (tableOf nodes (fun i => P.eval (nodes i))) = P.coeff m := by
  rw [recover_eq_evaluate nodes _ hi, Interpolation.evaluate_eq_coefficient nodes hi P hP]

@[simp] theorem recover_nil : recover ([] : Table K) = 0 := rfl

@[simp] theorem recover_singleton (node value : K) : recover [(node, value)] = value := by
  simp [recover, rowTerm, denominator, otherNodes]

/-- Zero values are preserved even on a table with repeated nodes. -/
theorem recover_zero (nodes : List K) : recover (nodes.map (fun x => (x, 0))) = 0 := by
  simp [recover, rowTerm, List.map_map, Function.comp_def]

end Counting.Algorithm.InterpolationMachine.Materialized
