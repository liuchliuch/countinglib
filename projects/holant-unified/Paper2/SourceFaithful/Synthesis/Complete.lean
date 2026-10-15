import Paper2.SourceFaithful.Synthesis.MountainCases
import Paper2.SourceFaithful.HighHeightCompleteTerminal
import Paper2.SourceFaithful.HeightOneComplete
import Paper2.Paper1ProvedUnaryProvider
import Paper2.Paper1ProvedProvider
import Paper2.Paper1ProvedGadgetProvider
import Paper2.Paper1ProvedRestrictionProvider
import Paper2.Paper1ProvedFactorProvider
import Paper2.Paper1ProvedNormalizationProvider
import Paper2.Paper1ProvedEOProvider
import Paper2.Paper1ProvedSingleWeightProvider
import Paper2.Paper1ProvedInterpolationProvider
import Paper2.Paper1ProvedOccurrenceProvider

/-! The completed height-four-and-above theorem consumes the exact retained
Section 9 route. Every original-language mountain branch is discharged by a
proved classification, with the same canonical field output and the actual
backward reduction from the prepared language. -/
namespace Paper2.SourceFaithful.Synthesis
open Tractable ExactInput

/-- The original finite language is hard or reaches a genuine retained
height-one mountain.  The larger-height alternative in `MountainCases` is
consumed internally by the complete high-height theorem. -/
theorem original_hard_or_height_one
    (P : Paper1Accepted) (PO : Paper1OddAccepted) (PE : Paper1EOAccepted)
    (PS : Paper1SingleWeightAccepted) (PD : Paper1DirectGadgetAccepted)
    (PF : Paper1FactorClosureAccepted) (PR : Paper1RestrictionAccepted)
    (PU : Paper1UnaryAccepted) (PN : Paper1NormalizationAccepted)
    (PC : Paper1OccurrenceAccepted) (PB : Paper1BinaryInterpolationAccepted)
    (L : Language) (hnot : ¬ Tract (kImage L)) :
    FixedFieldOutput.SharpPHard .nativeX L ∨
      ∃ A : OriginalMountainRoute L, A.prepared.height = 1 := by
  rcases original_hard_or_remaining_mountain P PO PE PS PD PF PR PU PN PC L hnot with
    hh | hremaining
  · exact Or.inl hh
  · obtain ⟨remaining⟩ := hremaining
    cases remaining with
    | heightOne A h1 => exact Or.inr ⟨A,h1⟩
    | heightAtLeastFour A h4 =>
      rcases HighHeight.classification_ge_four P PD PC PF PU PE PR PB PN
        A.prepared.language h4 A.prepared.preprocessed A.prepared.even A.prepared.divisible
        A.prepared.mountain A.prepared.isMountain A.prepared.member with ht | hh
      · exact False.elim (A.nontractable hnot ht)
      · exact Or.inl (A.transfer_hardness hh)

/-- Section 9's complete hardness direction. All heights are proved in this
project; the named remaining inputs are upstream Paper 1 source theorems.
The unary source theorem is derived from the odd theorem and restriction,
rather than supplied as an independent classification premise. -/
theorem native_hardness
    (P : Paper1Accepted) (PO : Paper1OddAccepted) (PE : Paper1EOAccepted)
    (PS : Paper1SingleWeightAccepted) (PD : Paper1DirectGadgetAccepted)
    (PF : Paper1FactorClosureAccepted) (PR : Paper1RestrictionAccepted)
    (PN : Paper1NormalizationAccepted) (PC : Paper1OccurrenceAccepted)
    (PB : Paper1BinaryInterpolationAccepted)
    (L : Language) (hnot : ¬ Tract (kImage L)) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  let PU := Paper2.Paper1Proved.unaryProviderOfOdd PO PR
  rcases original_hard_or_height_one P PO PE PS PD PF PR PU PN PC PB L hnot with
    hh | ⟨A,h1⟩
  · exact hh
  · have classify : ∀ (d : ℕ) (M : Signature AlgebraicComplex (2 * d)),
        d = 1 → IsMountain M →
        (⟨2 * d,M⟩ : AnySignature AlgebraicComplex) ∈ A.prepared.language.family →
        Tract (kImage A.prepared.language) ∨
          FixedFieldOutput.SharpPHard .nativeX A.prepared.language := by
      intro d M hd hM hmem
      subst d
      exact HeightOne.mountain_classification_preprocessed P PD PR PF PB PO PN
        A.prepared.language A.prepared.preprocessed M hM hmem
    rcases classify A.prepared.height A.prepared.mountain h1
      A.prepared.isMountain A.prepared.member with ht | hh
    · exact False.elim (A.nontractable hnot ht)
    · exact A.transfer_hardness hh

/-- Instantiation of every complete local source implementation. Only the
ordinary odd theorem remains an explicit
upstream argument; there is no supplied Paper 2 classification conclusion. -/
theorem native_hardness_with_proved_local
    (PO : Paper1OddAccepted)
    (L : Language) (hnot : ¬ Tract (kImage L)) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  exact native_hardness Paper2.Paper1Proved.provider PO Paper2.Paper1Proved.eoProvider
    (Paper2.Paper1Proved.singleWeightProvider Paper2.Paper1Proved.directGadgetProvider
      Paper2.Paper1Proved.factorProvider Paper2.Paper1Proved.eoProvider
      Paper2.Paper1Proved.restrictionProvider)
    Paper2.Paper1Proved.directGadgetProvider Paper2.Paper1Proved.factorProvider
    Paper2.Paper1Proved.restrictionProvider Paper2.Paper1Proved.normalizationProvider
    Paper2.Paper1Proved.occurrenceProvider Paper2.Paper1Proved.binaryInterpolationProvider L hnot

/-- The original ordinary graph problem has the same completed hardness
direction. Inverse K changes the literal tables and preserves every graph
byte and value through the proved canonical field conversion. -/
theorem ordinary_hardness_with_proved_local
    (PO : Paper1OddAccepted)
    (L : Language) (hnot : ¬ Tract L.family) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  apply ordinary_hard_iff_inverseK_native L |>.mpr
  apply native_hardness_with_proved_local PO (Paper2.Synthesis.inverseKLanguage L)
  simpa only [Paper2.Synthesis.kImage_inverseKLanguage] using hnot

/-- Both structural branches of the original ordinary fixed-language theorem
use actual implementations: the complete evaluation programme on the seven
tractable alternatives and the completed original-graph hardness reduction. -/
theorem ordinary_classification_with_proved_local
    (PO : Paper1OddAccepted) (L : Language) :
    (Tract L.family ∧ FixedFieldOutput.BooleanFP .ordinary L) ∨
      (¬ Tract L.family ∧ FixedFieldOutput.SharpPHard .ordinary L) := by
  classical
  by_cases ht : Tract L.family
  · exact Or.inl ⟨ht,Paper2.Paper1Proved.provider.evaluation_2_22 L ht⟩
  · exact Or.inr ⟨ht,ordinary_hardness_with_proved_local PO L ht⟩

end Paper2.SourceFaithful.Synthesis

