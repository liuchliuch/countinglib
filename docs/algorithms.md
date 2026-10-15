# Algorithms

CountingLib separates algorithm correctness, operation counts, representation
bounds, and concrete machine runtime. Each interface exposes the guarantees
proved for its actual input representation.

For the original algorithm literature, see
[references](references.md#selected-foundations-and-algorithm-literature).

| Algorithm | Public entry | Verified contract |
| --- | --- | --- |
| Lagrange interpolation | `Counting.Algorithm.Interpolation.Cost` | List/fold execution, coefficient recovery at distinct nodes, duplicate rejection, and query/field-operation counts |
| Encoded interpolation | `Counting.Algorithm.InterpolationMachine.Materialized.Machine` | Actual finite postprocessors and polynomial runtime over a fixed represented number field and basis |
| Pfaffian evaluation | `Counting.Algorithm.PfaffianFinite` | Signed-pairing correctness and a complete finite-stack evaluator with polynomial encoded runtime; field/basis fixed, order variable |
| FKT and Ising | `Counting.Algorithm.FKT.IsingPromise`, `.IsingUniform` | Fisher construction, computed orientation/sign, Pfaffian evaluation, normalization, and finite machines under the stated planar promises |
| Karp–Luby #DNF approximation | `Counting.Algorithm.KarpLubyRequest.Whole.Accuracy` | Whole raw-request finite machine, clean output, charged transition/Primitive bounds, and the finite fair-tape PAC/FPRAS contract |
| Variable elimination | `Counting.Algorithm.VariableElimination.Bridge` | Actual bucket elimination preserves the open partition for a supplied complete order |
| Cached elimination and width | `Counting.Algorithm.VariableEliminationWork.Inputs`, `Counting.Algorithm.VariableEliminationTreewidth.Program` | Direct addressing, cached layouts, accumulated declared logical work, and a supplied tree-decomposition-to-order/width bridge |
| Product evaluation | `Counting.Algorithm.Product`, `Counting.Algorithm.ProductFinitePalette.Machine` | S1 correctness and operation bounds; a fixed finite-palette factor frontend uses the original codec, solver, and runtime |
| Affine evaluation | `Counting.Algorithm.Affine`, `.FixedLanguage` | Boolean affine presentations, actual compiled bytecode, S1 correctness, and a separate fixed-language bit machine |
| Holographic transformation | `Counting.Algorithm.Holographic` | Closed invariance and open boundary covariance with explicit matrix directions; fixed-table machines are optional imports |
| CPOG counting | `Counting.Algorithm.CPOG.Bridge` | Original array counter and ring evaluator connected to S1 under partitionedness, variable coverage, and formula-equivalence premises |
| Exact field operations | `Counting.Algorithm.FieldArithmetic` | Canonical codecs and subtraction, division, and equality machines for a fixed field and basis |

## Interpret the cost model

Interpolation's arithmetic interface counts sample queries and field operations;
its encoded machine layer proves runtime for a fixed field representation.
Variable elimination charges its declared table, address, preparation, read,
and coefficient-operation channels. Scope/assignment internals, physical
allocation, coefficient bit costs, decomposition conversion, and decomposition
search are separate obligations.

The Affine S1 assembly is currently noncomputable; the independent fixed-language
machine uses its own explicit encoding. Holographic semantics applies to finite
domains, while the optional original machines have narrower fixed-table contracts.
Karp–Luby's probability guarantee uses its finite uniform random-tape model and
legal accuracy/confidence parameters; the runtime also charges their encodings.

## Extend the algorithm layer

New algorithms should provide an input model, output specification, actual
executor, correctness theorem, and the claimed cost or probability bound.
Prefer an existing model bridge and a meaningful downstream client.

Demand-driven directions include complete variable-elimination bit costs,
counting/sampling interfaces, Ryser execution refinements, JSV, Weitz correlation
decay, zero-free methods, and certified approximate model counting. These are
separate contracts from exact classification; see the [roadmap](roadmap.md).
