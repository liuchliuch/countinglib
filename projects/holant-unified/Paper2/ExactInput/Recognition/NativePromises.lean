import Paper2.ExactInput.Recognition.NativeUniform
import Paper2.ExactInput.NativeRecognition
import Paper2.Paper1ProvedProvider

/-! Literal restrictions of a global native recognizer to the two source
promise domains. Every restriction executes the same finite machine on the
same original descriptor bits; the promise changes only its correctness
proof. No transform, graph computation, or source classification is assumed. -/
namespace Paper2.ExactInput.Recognition
open Paper2.Problem

/-- The literal-I promise specializes the global criterion to TractX through
the proved equality-anchor theorem. -/
def equalityXRecognizer (r : NativeTractRecognizer) :
    EqualityNativeXRecognizer where
  decision L := r.decision L.val
  machine := {
    tm := r.machine.tm
    inputAlphabet := r.machine.inputAlphabet
    outputAlphabet := r.machine.outputAlphabet
    outputsFun L := r.machine.outputsFun L.val }
  finiteAlphabets := r.finiteAlphabets
  correct L := (r.correct L.val).trans
    (Paper2.Paper1Proved.provider.equalityAnchor_2_13 L.val L.property)

/-- The complete seven-clause criterion on the literal-I domain uses exactly
the same machine as the global native recognizer. -/
def equalityRecognizer (r : NativeTractRecognizer) :
    EqualityNativeTractRecognizer where
  decision L := r.decision L.val
  machine := {
    tm := r.machine.tm
    inputAlphabet := r.machine.inputAlphabet
    outputAlphabet := r.machine.outputAlphabet
    outputsFun L := r.machine.outputsFun L.val }
  finiteAlphabets := r.finiteAlphabets
  correct L := r.correct L.val

/-- Prime-quaternary recognition is a restriction of the same global machine;
it does not rely on a runtime test of the promise. -/
def primeQuaternaryRecognizer (r : NativeTractRecognizer) :
    PrimeQuaternaryNativeRecognizer where
  decision L := r.decision L.val
  machine := {
    tm := r.machine.tm
    inputAlphabet := r.machine.inputAlphabet
    outputAlphabet := r.machine.outputAlphabet
    outputsFun L := r.machine.outputsFun L.val }
  finiteAlphabets := r.finiteAlphabets
  correct L := r.correct L.val

/-- Both precisely named native source-recognition interfaces have actual
inhabitants whenever the global recognizer has been implemented. -/
theorem nativeAcceptedOfRecognizer (r : NativeTractRecognizer) :
    Paper1NativeRecognitionAccepted := {
  literalEqualityRecognition_1_2 := ⟨equalityXRecognizer r⟩
  primeQuaternaryRecognition_1_3 := ⟨primeQuaternaryRecognizer r⟩ }

end Paper2.ExactInput.Recognition

