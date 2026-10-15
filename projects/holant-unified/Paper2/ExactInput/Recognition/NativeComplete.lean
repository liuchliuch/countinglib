import Paper2.Paper1ProvedRecognition.NativeSource
import Paper2.ExactInput.Recognition.NativePromises
import Paper2.PublicDichotomyComplete

/-! The precisely named native source recognition interfaces are instantiated
with the proved global native machine. The accompanying complexity clauses
use the strict public graph and answer convention and have no source-provider
argument. -/
namespace Paper2.ExactInput.Recognition
open Paper2.Problem Paper2.Tractable
noncomputable section

/-- Actual implementations of both native source-recognition sentences. -/
theorem nativeRecognitionAccepted : Paper1NativeRecognitionAccepted :=
  nativeAcceptedOfRecognizer Paper1ProvedRecognition.NativeSource.recognizer

/-- Source Theorem 2.23, including recognition on the original native bits. -/
theorem literalEqualityDichotomyWithRecognition_2_23 :
    Nonempty EqualityNativeTractRecognizer ∧
      ∀ L : Language, HasLiteralEquality L →
        (Tract (kImage L) → Problem.InFP .nativeX L) ∧
        (¬Tract (kImage L) → Problem.SharpPHard .nativeX L) := by
  refine ⟨⟨equalityRecognizer Paper1ProvedRecognition.NativeSource.recognizer⟩,?_⟩
  intro L _
  exact ⟨TractableAlgorithms.native_public_inFP_of_tract L,
    PublicDichotomy.native_hardness L⟩

/-- Source Theorem 2.24, with the same proved global recognizer restricted to
the prime-quaternary domain. -/
theorem primeQuaternaryDichotomyWithRecognition_2_24 :
    Nonempty PrimeQuaternaryNativeRecognizer ∧
      ∀ L : Language, HasPrimeEightVertex L →
        (Tract (kImage L) → Problem.InFP .nativeX L) ∧
        (¬Tract (kImage L) → Problem.SharpPHard .nativeX L) := by
  refine ⟨⟨primeQuaternaryRecognizer Paper1ProvedRecognition.NativeSource.recognizer⟩,?_⟩
  intro L _
  exact ⟨TractableAlgorithms.native_public_inFP_of_tract L,
    PublicDichotomy.native_hardness L⟩

end
end Paper2.ExactInput.Recognition

