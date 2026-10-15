import Paper2.ExactInput.GadgetAugmentation
import Paper2.Tractable.Conformal

/-! One exact accepted Paper 1 Lemma 2.26 step: legal global GO(X)
normalization of a retained preprocessed literal language. Structural criterion
transport is proved from the seven definitions, not added to this interface. -/
namespace Paper2
open Tractable ExactInput

/-- Source Lemma 2.26's single legal global-coordinate step, specialized to the
actual root-code/graph languages. `XConformal` includes the nonzero edge scalar
and exact bilinear equation DᵀXD=μX. No arbitrary problem equivalence is allowed. -/
structure Paper1NormalizationAccepted where
  normalization_2_26 : ∀ L : Language, Preprocessed L.family →
    ∀ D : InvertibleKernel, XConformal D → ∀ M : Language,
      M.family = familyAction D L.family →
        Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M

namespace Paper1NormalizationAccepted

/-- Algebraic coordinate transport has a real finite literal input encoding. -/
theorem normalize (P : Paper1NormalizationAccepted) (L : Language)
    (hL : Preprocessed L.family) (D : InvertibleKernel) (hD : XConformal D) :
    ∃ M : Language, M.family = familyAction D L.family ∧
      Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M := by
  obtain ⟨M, hM⟩ := Language.coverage_family _ (L.family_finite.image _)
  exact ⟨M, hM, P.normalization_2_26 L hL D hD M hM⟩

end Paper1NormalizationAccepted

namespace Problem

/-- A true equivalence transports even the non-vacuous bounded-output witness:
no separate assumption about the target answer size is needed. -/
theorem SharpPHard.transport_equivalence {w : Wiring} {source target : Language}
    (hard : SharpPHard w source) (forward : Reduces w source target)
    (backward : Reduces w target source) : SharpPHard w target :=
  hard.transport forward (backward.sourceAnswers hard.1)

end Problem
end Paper2
