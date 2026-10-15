import Paper2.Paper1ProvedOddUnaryGeneralizedEqualityTerminal
import Paper2.Paper1ProvedOddUnaryWComplete
import Paper2.Paper1ProvedEOProvider

/-! The original unary classification has no structural consumer input.
The genuine independent-isotropic pair reaches a retained ternary or weighted
generalized equality graph; both are consumed by proved original-language
hardness routes with their executed canonical reductions. -/
namespace Paper2.Paper1Proved.OddUnary
open Paper2.Tractable Paper2.ExactInput
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnaryProvider

/-- The second independent original-isotropic unary completes the source
classification through actual finite retained languages and graph resources. -/
theorem provedPairConsumer : PairConsumer := by
  intro L hp hnot pair
  rcases IsotropicGeneralizedEqualityStage.hard_or_ternary_or_generalizedEquality
      Paper2.Paper1Proved.provider Paper2.Paper1Proved.directGadgetProvider
      Paper2.Paper1Proved.restrictionProvider Paper2.Paper1Proved.factorProvider
      Paper2.Paper1Proved.eoProvider Paper2.Paper1Proved.normalizationProvider
      L hp hnot pair with hh | ht | hge
  · exact hh
  · obtain ⟨S⟩ := ht
    rcases S.source.hard_or_isotropic_w Paper2.Paper1Proved.provider
        Paper2.Paper1Proved.directGadgetProvider Paper2.Paper1Proved.restrictionProvider
        Paper2.Paper1Proved.factorProvider Paper2.Paper1Proved.normalizationProvider with hh | hw
    · exact S.transfer_hard hh
    · exact S.transfer_hard (hw.elim (fun W=>W.hard))
  · exact hge.elim (fun S=>S.hard)

/-- The independent proved unary provider is constructed before the derived
odd theorem. No odd-classification input occurs in its definition. -/
theorem proved : SourceFaithful.Paper1UnaryAccepted :=
  providerOfResidualConsumers provedWConsumer provedPairConsumer

theorem native_classification (L : Language) (u : Signature AlgebraicComplex 1)
    (hu : u≠0) (hmem : (⟨1,u⟩ : AnySignature AlgebraicComplex)∈L.family) :
    Tract (Paper2.kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := proved.unary_3_4 L u hu hmem

end UnaryProvider
end
end Paper2.Paper1Proved.OddUnary

