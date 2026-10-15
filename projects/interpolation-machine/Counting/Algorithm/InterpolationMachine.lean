import Counting.Algorithm.InterpolationMachine.Materialized.Machine
import Counting.Algorithm.InterpolationMachine.Compiler
import Counting.Algorithm.InterpolationMachine.Graph
import Counting.Algorithm.InterpolationMachine.FieldSource

/-!
# Exact interpolation machines with explicit fixed-field encodings

`Compiler` starts with a unary degree and canonical field samples. `Graph` and
`FieldSource` supply the original graph bounds and source/oracle value contracts.
These fixed-schedule machines have Boolean work-stack alphabets.
`Materialized.Machine` instead accepts runtime node/sample tables, with total
polynomial bit time and ordinary Lagrange correctness on distinct nodes,
including zero. Its finite alphabet subtypes come from the canonical PH compiler.
Both branches fix the exact field and its rational basis; neither claims
arbitrary-field FP or identifies their different codecs without a proof.
-/
