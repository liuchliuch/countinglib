import PfaffianPort.OccurrencePfaffianEliminationAlgorithm

/-!
# Executable first-nonzero Pfaffian elimination and arithmetic schedule

This is the thin public program API for the fixed PlanarHom source at commit
`db68e745380769c38c8347736d2d84fcde38263c`, migrated under `PfaffianPort`.
It imports only the migrated kernel; the semantic equality with the literal
signed pairing sum is provided separately by `Semantics`.

`run` returns a value and counters for field arithmetic, zero tests, and successful
pivots. Each pivot materializes all `n * n` ambient entries, with two products,
two divisions, one subtraction and one addition per entry, followed by two
multiplications of the recursive scalar result. Hence the precise scheduled
field-operation count is `(6 * n * n + 2) * pivots`.

The zero-test counter follows the first-nonzero scan: a pivot at zero-based tail
position `k` takes `k + 1` tests, and failure takes the whole tail length. An empty
active list returns one with zero counters; a nonempty list without a pivot
returns zero without updating the matrix. Every successful pivot removes two
active vertices. The ambient matrix dimension remains unchanged.

These counters describe source-level field operations. Indexing, allocation,
parity, natural-number bookkeeping, and representation-dependent field-operation
costs are outside the arithmetic counter. The exported bounds are not bit-time
or finite-machine complexity theorems. A general active list is executable;
semantic correctness has additional skew, zero-diagonal, and order hypotheses.
-/

namespace Counting.Algorithm.Pfaffian

export PfaffianPort.MultiGraph.PfaffianElimination
  (RunResult firstPivot firstPivot_nil firstPivot_none_iff firstPivot_some_spec
   firstPivot_nonzero firstPivot_index_lt
   pivotUpdate pivotUpdate_skew pivotUpdate_diag
   materialize materialize_apply materialize_eq storedUpdate storedUpdate_eq
   pivotSign pivotSign_eq stepArithmetic
   run run_nil run_cons_noPivot run_cons_pivot
   run_schedule_bounds run_arithmetic_le_cubic run_zeroTests_le_square)

end Counting.Algorithm.Pfaffian
