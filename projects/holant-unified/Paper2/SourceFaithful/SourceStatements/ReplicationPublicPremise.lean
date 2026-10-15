import Paper2.SourceFaithful.SourceStatements.PublicReduction
import Paper2.FixedFieldOutput.OccurrenceReductions
import Paper2.RelativeEO.OccurrenceReductions

/-! The designated-occurrence selector premise is converted by the same
executed strict-root decoder used for the public unrestricted reductions. -/
namespace Paper2.SourceFaithful.SourceStatements.Replication
open Computability Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Paper2.Complexity BinaryCompose FixedRootCodec Paper2.TractableAlgorithms
open Paper2.RelativeEO
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem public_one_to_fixed (w : Wiring) (L : Language) {n : ℕ}
    (g : Signature AlgebraicComplex n)
    (one : RelativeEO.TaggedReduces w L g (fun k => k=1) L) :
    FixedFieldOutput.TaggedReduces w L g (fun k => k=1) L := by
  obtain ⟨answers,⟨r⟩⟩ := one (TractableAlgorithms.publicBoundedAnswers w L)
  let T := tagged L g
  let decode := reverseRootCoordinates T.fieldPresentation (fieldEmbedding T)
  have he : ∀ G : TaggedInstance L g (fun k => k=1),
      decode (answers.answer G)=FixedFieldOutput.taggedAnswer w L g (fun k => k=1) G := by
    intro G
    have hx : fieldEmbedding T (T.fieldPresentation.decode
        (FixedFieldOutput.answer w T G.val))=(value w T G.val : ℂ) :=
      congrArg (fun z : AlgebraicComplex => (z : ℂ)) (FixedFieldOutput.answer_correct w T G.val)
    have hc := answers.correct G
    rw [← hx] at hc
    simpa [decode,FixedFieldOutput.taggedAnswer] using reverseRootCoordinates_correct T.fieldPresentation (fieldEmbedding T)
      (answers.answer G) (T.fieldPresentation.decode (FixedFieldOutput.answer w T G.val)) hc
  let first := OracleDecode.reduction
    (reverseRootCoordinatesComputes T.fieldPresentation (fieldEmbedding T)) answers.outputBound he
  exact ⟨first.controlledCompose (r.controlledCompose (PublicReduction.forward w L))⟩


end
end Paper2.SourceFaithful.SourceStatements.Replication
