import Counting.Algorithm.InterpolationMachine.Graph
import Holant.Proofs.BinaryInterpolation.FieldSource

/-!
# The original graph source, in its fixed exact field

The spectral pencil supplies node separation and nonzero scaling. Its canonical
rational-coordinate codec is retained for the source answer, oracle answer and
machine output. No natural-valued counting class is inferred from this codec.
-/
namespace Counting.Algorithm.InterpolationMachine.FieldSource

open Turing Computability Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryInterpolation
namespace Source
export Holant.LocalDrafts.BinaryInterpolation.FieldSource
  (Field fixedField data Input inputEncoding outputEncoding targetEncoding asMacroInput
   targetTables gamma rho reduction execution_certificate denominator_nonzero recovery)
end Source
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Holant.Signature ℂ (arity i.val))
variable (halg : ∀ i x, IsAlgebraic ℚ (G i x))
variable {B : Holant.Certificates.MatchingContractionClosure.Binary (K:=ℂ)} (M : AlgebraicSource.Macro G B)
variable (p : AlgebraicSource.Pencil M.binary)

/-- The publicly executable I1 value is exactly the original Γ∪{H} graph value. -/
theorem evaluate_eq_source (r : Source.Input (s:=s) (arity:=arity)) :
    Graph.value (Source.data G halg M p) (Source.asMacroInput G M r) =
      AlgebraicSource.CommonField.sourceValue G M.binary p r := by
  rw [← Graph.interpolated_eq_value (Source.data G halg M p) (Source.asMacroInput G M r)]
  · exact Source.recovery G halg M p r
  · exact AlgebraicSource.CommonField.positive_nodes_injective G M.binary p _
  · exact AlgebraicSource.CommonField.beta_nonzero G M.binary p

/-- The actual postprocessor returns the original source value, with its original
polynomial bound and canonical field codec. Its answers are the real graph queries. -/
def post_outputs_source (r : Source.Input (s:=s) (arity:=arity)) :
    TM2OutputsInTime (Graph.MC.post (Source.data G halg M p)).computer
      ((Graph.MC.answerEncoding (F:=Source.fixedField G halg M p)).encode
        (Graph.MC.answered (Source.data G halg M p) (Source.asMacroInput G M r)))
      (some ((Source.outputEncoding G halg M p).encode
        (AlgebraicSource.CommonField.sourceValue G M.binary p r)))
      ((Graph.MC.postTime (Source.data G halg M p)).eval
        ((Source.inputEncoding (s:=s) (arity:=arity)).encode r).length) := by
  have h := Graph.MC.post_outputs (Source.data G halg M p) (Source.asMacroInput G M r)
  rw [Source.recovery] at h
  exact h

/-- The source theorem's nonzero denominator is independent of its output value. -/
theorem division_safe (r : Source.Input (s:=s) (arity:=arity)) :
    (Graph.MC.resultPair (Source.data G halg M p) (Source.asMacroInput G M r)).2 ≠ 0 :=
  Source.denominator_nonzero G halg M p r

end
end Counting.Algorithm.InterpolationMachine.FieldSource
