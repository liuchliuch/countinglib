import Paper2.SourceFaithful.PublicHardness
import Paper2.ExactInput.Reductions

/-! Exact selector-reduction transport through the two executed output codecs.
The public target convention may use any correct polynomial-length minimal
root descriptions. The reverse decoder is correct on all such descriptions,
and the forward converter supplies a fixed correct source convention. -/
namespace Paper2.SourceFaithful.SourceStatements.PublicReduction
open Computability Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Paper2.Complexity BinaryCompose FixedRootCodec
open Paper2.TractableAlgorithms
noncomputable section

def forward (w : Wiring) (L : Language) :
    LengthControlledOracleReduction (inputEncoding L) rootEncoding
      (inputEncoding L) (FixedFieldOutput.answerEncoding L)
      (publicAnswer w L) (FixedFieldOutput.answer w L) :=
  OracleDecode.reduction (coordinateRootComputes L.fieldPresentation (fieldEmbedding L))
    (FixedFieldOutput.outputBound w L) (fun _ => rfl)

def reverse (w : Wiring) (L : Language) (answers : BoundedAnswers w L) :
    LengthControlledOracleReduction (inputEncoding L) (FixedFieldOutput.answerEncoding L)
      (inputEncoding L) rootEncoding (FixedFieldOutput.answer w L) answers.answer := by
  let decode := reverseRootCoordinates L.fieldPresentation (fieldEmbedding L)
  have he : ∀ G, decode (answers.answer G) = FixedFieldOutput.answer w L G := by
    intro G
    have hx : fieldEmbedding L
        (L.fieldPresentation.decode (FixedFieldOutput.answer w L G)) = (value w L G : ℂ) :=
      congrArg (fun z : AlgebraicComplex => (z : ℂ)) (FixedFieldOutput.answer_correct w L G)
    have hc := answers.correct G
    rw [← hx] at hc
    simpa using reverseRootCoordinates_correct L.fieldPresentation (fieldEmbedding L)
      (answers.answer G) (L.fieldPresentation.decode (FixedFieldOutput.answer w L G)) hc
  exact OracleDecode.reduction
    (reverseRootCoordinatesComputes L.fieldPresentation (fieldEmbedding L)) answers.outputBound he

/-- Every actual canonical reduction is a public strict-root selector
reduction, uniformly over arbitrary correct bounded target conventions. -/
theorem of_fixed_field (w : Wiring) (source target : Language)
    (h : FixedFieldOutput.Reduces w source target) : Problem.Reduces w source target := by
  obtain ⟨r⟩ := h
  intro answers
  exact ⟨publicBoundedAnswers w source,
    ⟨(forward w source).controlledCompose (r.controlledCompose (reverse w target answers))⟩⟩

/-- Conversely, instantiate a public selector reduction with the executed
forward codec, then execute the source reverse codec. No oracle convention
is assumed computable merely from its correctness or its polynomial size. -/
theorem to_fixed_field (w : Wiring) (source target : Language)
    (h : Problem.Reduces w source target) : FixedFieldOutput.Reduces w source target := by
  obtain ⟨answers,⟨r⟩⟩ := h (publicBoundedAnswers w target)
  exact ⟨(reverse w source answers).controlledCompose (r.controlledCompose (forward w target))⟩

theorem reduces_iff_fixed_field (w : Wiring) (source target : Language) :
    Problem.Reduces w source target ↔ FixedFieldOutput.Reduces w source target :=
  ⟨to_fixed_field w source target,of_fixed_field w source target⟩

end
end Paper2.SourceFaithful.SourceStatements.PublicReduction

