import Paper2.ExactInput.CoordinateOutputBound
import Paper2.Complexity.BellMachines.BinaryCompose.Interface

/-! Source-faithful chosen-number-field output convention. The input language
still consists of strict exact root-coded tables. Graph input bytes and values
are unchanged. Only answers use canonical rational coordinates in the fixed
coefficient field selected before any graph is read. This module makes no
claim about polynomial conversion to or from public isolated-root answers. -/
namespace Paper2.FixedFieldOutput
open Paper2.Tractable Computability Paper2.Complexity Paper2.ExactInput Paper2.Problem Paper2.Algebraic

abbrev Answer (L : Language) := Fin (Module.finrank ℚ L.coefficientField) → ℚ
noncomputable abbrev answerEncoding (L : Language) : Encoding (Answer L) Bool :=
  vectorEncoding (Module.finrank ℚ L.coefficientField)
noncomputable abbrev answer (w : Wiring) (L : Language) : Instance L → Answer L :=
  outputCoordinates w L

/-- Standard finite-alphabet bit-time FP, kept distinct from the explicit
Boolean-stack normal-form witness used by the compiler API. -/
def InFP (w : Wiring) (L : Language) : Prop :=
  Complexity.InFP (inputEncoding L) (answerEncoding L) (answer w L)

/-- Concrete composable finite Boolean-stack evaluation. This entails `InFP`;
no reverse normal-form compiler is silently assumed here. -/
def BooleanFP (w : Wiring) (L : Language) : Prop :=
  Nonempty (BinaryCompose.Computes (inputEncoding L) (answerEncoding L) (answer w L))

theorem BooleanFP.inFP {w : Wiring} {L : Language} (h : BooleanFP w L) : InFP w L := by
  obtain ⟨m⟩ := h
  exact m.inFP

/-- The selected canonical answer is unique and has a proved polynomial bound,
so this target oracle convention is nonvacuous without an extra hypothesis. -/
noncomputable def outputBound (w : Wiring) (L : Language) :
    PolynomialOutputBound (inputEncoding L) (answerEncoding L) (answer w L) :=
  coordinateOutputBound w L

def SharpPHard (w : Wiring) (L : Language) : Prop :=
  ∀ f : List Bool → ℕ, InSharpP (encodingList Bool) f →
    Nonempty (LengthControlledOracleReduction (encodingList Bool) encodingNatBool
      (inputEncoding L) (answerEncoding L) f (answer w L))

/-- Actual length-controlled Turing reduction between canonical field answers. -/
def Reduces (w : Wiring) (source target : Language) : Prop :=
  Nonempty (LengthControlledOracleReduction (inputEncoding source) (answerEncoding source)
    (inputEncoding target) (answerEncoding target) (answer w source) (answer w target))

 theorem answer_correct (w : Wiring) (L : Language) (G : Instance L) :
    (L.fieldPresentation.decode (answer w L G) : AlgebraicComplex) = value w L G :=
  outputCoordinates_spec w L G

 theorem answer_unique (w : Wiring) (L : Language) (G : Instance L) (v : Answer L)
    (hv : (L.fieldPresentation.decode v : AlgebraicComplex) = value w L G) :
    v = answer w L G := by
  apply L.fieldPresentation.decode_injective
  apply Subtype.ext
  exact hv.trans (answer_correct w L G).symm

end Paper2.FixedFieldOutput
