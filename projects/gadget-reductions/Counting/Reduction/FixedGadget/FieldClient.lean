import Counting.Reduction.FixedGadget.ExactField
import Counting.Reduction.FixedGadget.Client

/-! The same nontrivial repeated macro graph uses the exact coefficient oracle
endpoint, retaining its original faithful field output encoding. -/
namespace Counting.Reduction.FixedGadget.FieldClient
open Holant Holant.Algebraic Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Computability RawClosedNetwork Client
noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
variable (F : FixedField K n) (T : ExactSignatureTables n 1 1 Client.arity)

/-- The concrete graph has two macro occurrences and four emitted base vertices. -/
theorem repeated_exact : T.evaluate F Client.output =
    (exactSource F Client.templates Client.templates_valid T).evaluate F Client.repeated :=
  exact_value F Client.templates Client.templates_valid T Client.repeated

/-- A real oracle execution on the original graph bytes returns the exact macro
value. The oracle agrees only on valid base inputs; malformed words remain arbitrary. -/
def repeated_oracle_run (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (validatedEncoding 1 1 Client.arity) F.encoding (T.evaluate F) oracle) :
    (exactReduction F Client.templates Client.templates_valid T).machine.OutputsInTime oracle
      ((validatedEncoding 2 1 (sourceArity Client.templates)).encode Client.repeated)
      (F.encoding.encode
        ((exactSource F Client.templates Client.templates_valid T).evaluate F Client.repeated))
      ((exactReduction F Client.templates Client.templates_valid T).time.eval
        ((validatedEncoding 2 1 (sourceArity Client.templates)).encode Client.repeated).length) :=
  (exactReduction F Client.templates Client.templates_valid T).correct oracle ho Client.repeated
end
end Counting.Reduction.FixedGadget.FieldClient
