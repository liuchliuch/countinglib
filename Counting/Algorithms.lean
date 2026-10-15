import Counting.Algorithm.Interpolation.Cost
import Counting.Algorithm.InterpolationMachine.Materialized.Machine
import Counting.Algorithm.Product
import Counting.Algorithm.CPOG.Bridge
import Counting.Algorithm.Affine
import Counting.Algorithm.Holographic
import Counting.Algorithm.Pfaffian.Evaluator
import Counting.Algorithm.PfaffianFinite
import Counting.Algorithm.FKT.IsingPromise
import Counting.Algorithm.FKT.IsingUniform
import Counting.Algorithm.KarpLuby.Guarantee
import Counting.Algorithm.KarpLuby.MedianCost
import Counting.Algorithm.KarpLuby.EncodedBounds
import Counting.Algorithm.KarpLubyMachine
import Counting.Algorithm.KarpLubyRequest.Whole.Accuracy
import Counting.Algorithm.VariableElimination.Bridge
import Counting.Algorithm.VariableElimination.MeasuredOrder
import Counting.Algorithm.VariableEliminationLayout.Program
import Counting.Algorithm.VariableEliminationLayout.Batch
import Counting.Algorithm.VariableEliminationWork.Inputs
import Counting.Algorithm.VariableEliminationWork.Address
import Counting.Algorithm.VariableEliminationWidth.Program
import Counting.Algorithm.VariableEliminationTreewidth.Program
import Counting.Adapters.VariableElimination
import Counting.Adapters.KarpLuby
import Counting.Adapters.Pfaffian

/-! Optional algorithms and their shared-library adapters.

Each algorithm retains its own verified complexity scope. In particular, the
Karp–Luby whole-request finite machine connects the original fair-tape PAC
guarantee to actual clean halts and polynomial transition/primitive bounds in
the deterministic request size plus inverse accuracy. The full
Pfaffian row evaluator now has a finite-stack F1 machine over each fixed
represented number field, retaining its actual input and output encodings.
Variable elimination includes cached layouts and complete-order observations of
coefficient operations, cached reads, preparation and materialization. Scope/assignment
function internals and bit costs remain separate. A supplied leaf-attachment bag
tree now constructs the elimination order and bounds seven execution-work channels
by the induced width. A supplied standard finite graph tree decomposition now
constructs that bag tree and derives primal factor coverage. Decomposition search
and conversion costs remain separate. Dynamic interpolation over a fixed represented
number field uses the actual finite polynomial-time postprocessor. CPOG counting retains its partitioned/coverage/equivalence premises. The complete
FKT Ising pipeline supplies finite machines for typed inputs, ordinary raw
planar promises, and graph/coupling pairs over a fixed represented field. The affine
fixed-language machine is imported separately from its mathematical S1 API.
-/
