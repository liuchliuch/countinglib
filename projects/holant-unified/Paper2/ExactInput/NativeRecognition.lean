import Paper2.Paper1Accepted

/-! The decidability sentences of Paper 1 Theorems 1.2 and 1.3, kept as exact
separate named accepted inputs. Official source checked at
https://arxiv.org/pdf/2609.00219v1, printed pages 7 and 8;
see docs/NATIVE_RECOGNITION_SOURCE.md. Machines read the native language's literal
minimal-root table bits. Their domains carry only the source theorem's promise;
there is no claimed effective K-image conversion or test of that promise. -/
namespace Paper2
open Tractable ExactInput Paper2.Complexity
open Computability

/-- Literal original native inputs under the precise equality-present promise. -/
abbrev EqualityNativeInput := {L : Language // HasLiteralEquality L}

/-- Literal original native inputs under the precise prime-quaternary promise. -/
abbrev PrimeQuaternaryNativeInput := {L : Language // HasPrimeEightVertex L}

/-- The actual reduced-criterion recognizer asserted in Paper 1 Theorem 1.2. -/
structure EqualityNativeXRecognizer where
  decision : EqualityNativeInput → Bool
  machine : Turing.TM2Computable (fun L : EqualityNativeInput => L.val.bits)
    encodingBoolBool.encode decision
  finiteAlphabets : ∀ k, Fintype (machine.tm.Γ k)
  correct : ∀ L, decision L = true ↔ TractX (kImage L.val)

/-- The seven-clause version produced from the source recognizer and anchor lemma. -/
structure EqualityNativeTractRecognizer where
  decision : EqualityNativeInput → Bool
  machine : Turing.TM2Computable (fun L : EqualityNativeInput => L.val.bits)
    encodingBoolBool.encode decision
  finiteAlphabets : ∀ k, Fintype (machine.tm.Γ k)
  correct : ∀ L, decision L = true ↔ Tract (kImage L.val)

/-- The actual full-criterion recognizer asserted in Paper 1 Theorem 1.3. -/
structure PrimeQuaternaryNativeRecognizer where
  decision : PrimeQuaternaryNativeInput → Bool
  machine : Turing.TM2Computable (fun L : PrimeQuaternaryNativeInput => L.val.bits)
    encodingBoolBool.encode decision
  finiteAlphabets : ∀ k, Fintype (machine.tm.Γ k)
  correct : ∀ L, decision L = true ↔ Tract (kImage L.val)

/-- Only the two explicitly sourced decidability sentences; no inhabitant is
postulated and no Paper 2 terminal or hardness conclusion occurs in this record. -/
structure Paper1NativeRecognitionAccepted where
  /-- Paper 1 Theorem 1.2: its four-clause native criterion is decidable. -/
  literalEqualityRecognition_1_2 : Nonempty EqualityNativeXRecognizer
  /-- Paper 1 Theorem 1.3: its seven-clause native criterion is decidable. -/
  primeQuaternaryRecognition_1_3 : Nonempty PrimeQuaternaryNativeRecognizer

namespace Paper1Accepted

/-- Exactly the same finite machine decides the seven-clause predicate once the
literal-I anchor specialization is proved or supplied by Paper 1 Lemma 2.13. -/
def equalityRecognizer (P : Paper1Accepted) (r : EqualityNativeXRecognizer) :
    EqualityNativeTractRecognizer where
  decision := r.decision
  machine := r.machine
  finiteAlphabets := r.finiteAlphabets
  correct L := (r.correct L).trans (P.equalityAnchor_2_13 L.val L.property).symm

/-- Complete classification-and-recognition interface for Paper 2 Theorem 2.23.
Both accepted records remain visible parameters. -/
theorem literalEqualityDichotomyWithRecognition_2_23
    (P : Paper1Accepted) (R : Paper1NativeRecognitionAccepted) :
    Nonempty EqualityNativeTractRecognizer ∧
      ∀ L : Language, HasLiteralEquality L →
        (Tract (kImage L) → Problem.InFP .nativeX L) ∧
        (¬ Tract (kImage L) → Problem.SharpPHard .nativeX L) := by
  obtain ⟨r⟩ := R.literalEqualityRecognition_1_2
  exact ⟨⟨P.equalityRecognizer r⟩, P.literalEqualityDichotomy_2_23⟩

/-- Complete classification-and-recognition interface for Paper 2 Theorem 2.24. -/
theorem primeQuaternaryDichotomyWithRecognition_2_24
    (P : Paper1Accepted) (R : Paper1NativeRecognitionAccepted) :
    Nonempty PrimeQuaternaryNativeRecognizer ∧
      ∀ L : Language, HasPrimeEightVertex L →
        (Tract (kImage L) → Problem.InFP .nativeX L) ∧
        (¬ Tract (kImage L) → Problem.SharpPHard .nativeX L) :=
  ⟨R.primeQuaternaryRecognition_1_3, P.primeQuaternaryDichotomy_2_24⟩

end Paper1Accepted
end Paper2
