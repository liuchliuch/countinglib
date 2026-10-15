import Paper2.FixedFieldOutput.Problem
import Paper2.Paper1Accepted

/-! Exact authorized Paper 1 classification inputs under the source's chosen
number-field answer convention. This is an additive interface, with no value
and no axiom. The older strict-root interface remains a separate, stronger
conditional contract. No root/field conversion or Paper 2 theorem is accepted.
The algorithmic fields explicitly choose ordinary finite Boolean work stacks as
the standard bit model; no formal reverse `PolyTime → BooleanFP` is inferred. -/
namespace Paper2.SourceFaithful
open Tractable ExactInput

structure Paper1Accepted where
  recognition_2_22 : Nonempty Problem.TractRecognizer
  evaluation_2_22 : ∀ L : Language, Tract L.family → FixedFieldOutput.BooleanFP .ordinary L
  literalEquality_1_2 : ∀ L : Language, HasLiteralEquality L →
    (TractX (kImage L) → FixedFieldOutput.BooleanFP .nativeX L) ∧
    (¬ TractX (kImage L) → FixedFieldOutput.SharpPHard .nativeX L)
  equalityAnchor_2_13 : ∀ L : Language, HasLiteralEquality L →
    (Tract (kImage L) ↔ TractX (kImage L))
  primeQuaternary_1_3 : ∀ L : Language, HasPrimeEightVertex L →
    (Tract (kImage L) → FixedFieldOutput.BooleanFP .nativeX L) ∧
    (¬ Tract (kImage L) → FixedFieldOutput.SharpPHard .nativeX L)

namespace Paper1Accepted

theorem recognitionAndEvaluation_2_18 (P : Paper1Accepted) :
    Nonempty Problem.TractRecognizer ∧
      ∀ L : Language, Tract L.family → FixedFieldOutput.BooleanFP .ordinary L :=
  ⟨P.recognition_2_22,P.evaluation_2_22⟩

theorem literalEqualityDichotomy_2_23 (P : Paper1Accepted) (L : Language)
    (h : HasLiteralEquality L) :
    (Tract (kImage L) → FixedFieldOutput.BooleanFP .nativeX L) ∧
    (¬ Tract (kImage L) → FixedFieldOutput.SharpPHard .nativeX L) := by
  obtain ⟨easy,hard⟩ := P.literalEquality_1_2 L h
  exact ⟨fun ht => easy ((P.equalityAnchor_2_13 L h).mp ht),
    fun ht => hard (fun hx => ht ((P.equalityAnchor_2_13 L h).mpr hx))⟩

end Paper1Accepted
end Paper2.SourceFaithful
