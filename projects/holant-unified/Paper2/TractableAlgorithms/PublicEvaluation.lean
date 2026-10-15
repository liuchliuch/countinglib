import Paper2.TractableAlgorithms.Paper1Evaluation
import Paper2.ExactInput.FixedRootCodec.ReturnedRoot

/-! Unconditional exact original-graph evaluation with the manuscript's public
monic irreducible polynomial and isolating rational rectangle. The fixed-field
evaluator, minimal-polynomial circuit, bisection circuits and final byte wiring
are all actual finite programs with proved polynomial transition bounds. -/
namespace Paper2.TractableAlgorithms
open Computability Paper2.Algebraic Paper2.Complexity
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open BinaryCompose FixedFieldMachines ExactInput.FixedRootCodec
noncomputable section

def fieldEmbedding (L : Language) : L.coefficientField →ₐ[ℚ] ℂ :=
  (algebraicClosure ℚ ℂ).val.comp L.coefficientField.val

def publicAnswer (w : Wiring) (L : Language) (G : Instance L) : RootCode :=
  coordinateRootCode L.fieldPresentation (fieldEmbedding L) (FixedFieldOutput.answer w L G)

theorem publicAnswer_correct (w : Wiring) (L : Language) : CorrectAnswers w L (publicAnswer w L) := by
  intro G
  have h := coordinateRootCode_correct L.fieldPresentation (fieldEmbedding L)
    (FixedFieldOutput.answer w L G)
  have he : fieldEmbedding L
      (L.fieldPresentation.decode (FixedFieldOutput.answer w L G)) = (value w L G : ℂ) :=
    congrArg (fun z : AlgebraicComplex => (z : ℂ)) (FixedFieldOutput.answer_correct w L G)
  rw [he] at h
  exact h

def publicComputes (w : Wiring) (L : Language)
    (m : Computes (inputEncoding L) (FixedFieldOutput.answerEncoding L)
      (FixedFieldOutput.answer w L)) :
    Computes (inputEncoding L) rootEncoding (publicAnswer w L) :=
  congrComputes (m.andThen (coordinateRootComputes L.fieldPresentation (fieldEmbedding L)))
    (fun _ => rfl)

theorem public_inFP_of_booleanFP (w : Wiring) (L : Language)
    (h : FixedFieldOutput.BooleanFP w L) : Problem.InFP w L := by
  obtain ⟨m⟩ := h
  exact ⟨publicAnswer w L,publicAnswer_correct w L,(publicComputes w L m).inFP⟩

/-- The bounded strict oracle convention exists for every original language,
including nontractable languages. Its bit bound composes proved coordinate
growth with the actual strict converter's output bound. -/
def publicBoundedAnswers (w : Wiring) (L : Language) : BoundedAnswers w L where
  answer := publicAnswer w L
  correct := publicAnswer_correct w L
  outputBound := {
    bound := (coordinateRootComputes L.fieldPresentation (fieldEmbedding L)).outputBound.bound.comp
      (coordinateOutputPolynomial w L)
    length_le G := by
      have hm := (coordinateRootComputes L.fieldPresentation (fieldEmbedding L)).outputBound.length_le
        (FixedFieldOutput.answer w L G)
      have hl := coordinate_output_length_le w L G
      apply hm.trans
      rw [Polynomial.eval_comp]
      exact natPolynomial_eval_mono _ hl }

theorem ordinary_public_inFP_of_tract (L : Language) (h : Tract L.family) :
    Problem.InFP .ordinary L :=
  public_inFP_of_booleanFP .ordinary L (ordinary_booleanFP_of_tract L h)

theorem native_public_inFP_of_tract (L : Language) (h : Tract (kImage L)) :
    Problem.InFP .nativeX L :=
  public_inFP_of_booleanFP .nativeX L (native_booleanFP_of_tract L h)

theorem native_public_inFP_of_tractX (L : Language) (h : TractX (kImage L)) :
    Problem.InFP .nativeX L := native_public_inFP_of_tract L h.tract

theorem ordinary_public_inFP_of_seven_alternatives (L : Language)
    (h : TractCore (preprocess L.family)) : Problem.InFP .ordinary L :=
  public_inFP_of_booleanFP .ordinary L (ordinary_booleanFP_of_seven_alternatives L h)

theorem native_public_inFP_of_seven_alternatives (L : Language)
    (h : TractCore (preprocess (kImage L))) : Problem.InFP .nativeX L :=
  public_inFP_of_booleanFP .nativeX L (native_booleanFP_of_seven_alternatives L h)

end
end Paper2.TractableAlgorithms
