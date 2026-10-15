import Counting.Reduction.FixedGadget.Machine
import Holant.Complexity.FixedGadgetSubstitution.TemplateFamily
import Holant.Complexity.OracleOneQuery.Reduction
import Holant.Complexity.BinaryCompose.Identity
import Holant.Complexity.OracleReductionCompose

/-! Exact coefficient-coordinate answers. The one-query program returns its
answer unchanged; all copying is charged using the proved target answer bound. -/
namespace Counting.Reduction.FixedGadget
open Holant Holant.Algebraic Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Computability RawClosedNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {n sourceCount s b : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K n) (templates : ℕ → Template)
variable (hg : ∀ i < sourceCount, (templates i).WellFormed s b arity)
variable (T : ExactSignatureTables n s b arity)

/-- The fixed extended family is the actual exact macro table in the same field. -/
abbrev exactSource := sourceTables templates T (templateCoordinates F templates hg T)

/-- The target evaluation at the actual compiled input equals the source value. -/
theorem exact_value (r : Input sourceCount b (sourceArity templates)) :
    T.evaluate F (compile templates hg r) = (exactSource F templates hg T).evaluate F r := by
  apply value_compile templates hg
    (fun i x => F.decode (templateCoordinates F templates hg T i x))
    (fun i x => F.decode (T.vertex i x)) (fun i x y => F.decode (T.edge i x y))
  intro i
  funext x
  exact (decode_templateCoordinates F templates hg T i x).symm

/-- One exact query, no projective scale or output recovery. Query compilation,
answer copying, and postprocessing all retain proved bit-machine bounds. -/
def exactReduction : PolyTimeOracleReduction
    (validatedEncoding sourceCount b (sourceArity templates)) F.encoding
    (validatedEncoding s b arity) F.encoding
    ((exactSource F templates hg T).evaluate F) (T.evaluate F) := by
  let r := OracleOneQuery.reduction (computes templates hg)
    (BinaryCompose.identityComputes F.encoding) (T.outputBound F)
  exact {
    machine := r.machine
    time := r.time
    correct := fun oracle ho x => by
      simpa only [Function.comp_apply, id_eq, exact_value] using r.correct oracle ho x }

/-- The concrete polynomial charges target reply length, rather than treating
oracle output copying as a constant-cost operation. -/
theorem exactReduction_time : (exactReduction F templates hg T).time =
    (computes templates hg).time + 1 +
      2 * (OracleOneQuery.answerBound (computes templates hg) (T.outputBound F) + 1) +
      (BinaryCompose.identityComputes F.encoding).time.comp
        (OracleOneQuery.answerBound (computes templates hg) (T.outputBound F)) := rfl

/-- FP transport uses actual ordinary-machine composition, independent of oracle inlining. -/
theorem exact_inFP_of_base
    (base : InFP (validatedEncoding s b arity) F.encoding (T.evaluate F)) :
    InFP (validatedEncoding sourceCount b (sourceArity templates)) F.encoding
      ((exactSource F templates hg T).evaluate F) :=
  Computation.InFP.congr (Computation.InFP.comp (compiler_inFP templates hg) base)
    (exact_value F templates hg T)

/-- Existing length-controlled callers may inline this exact reduction. -/
def exactHardnessTransport {α β : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    {f : α → β}
    (caller : LengthControlledOracleReduction ea eb
      (validatedEncoding sourceCount b (sourceArity templates)) F.encoding f
      ((exactSource F templates hg T).evaluate F)) :
    PolyTimeOracleReduction ea eb (validatedEncoding s b arity) F.encoding f (T.evaluate F) :=
  caller.compose (exactReduction F templates hg T)
end
end Counting.Reduction.FixedGadget
