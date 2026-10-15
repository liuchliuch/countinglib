import Paper2.RelativeEO.ComplementaryExit
import Paper2.SourceFaithful.OccurrenceInputs
import Paper2.SourceFaithful.RelativeEO.DirectedPairFactors

/-! Canonical fixed-field answer version of the proved local construction.
The pure signatures/networks are unchanged. Machine reductions are proved again
from the separately named source-exact records; no output-code conversion or
old strict-root classification is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.SourceFaithful.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.RelativeEO

theorem directedPair_access_of_complementaryE (P : Paper1OccurrenceAccepted) (L : Language)
    (hE : (⟨4, complementaryE⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    FixedFieldOutput.Reduces .nativeX (tagged L directedPair) L :=
  replicate_directed_pair P L _ (complementaryCarrierContext L hE) (tagged_family L directedPair)

/-- Both literal unit pins are obtained in a retained finite exact-input
augmentation, after the two-sided hypothesis legitimately enables factor closure. -/
theorem complementaryE_supplies_pins (P : Paper1OccurrenceAccepted)
    (F : Paper1FactorClosureAccepted) (L : Language)
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hE : (⟨4, complementaryE⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ N : Language, L.family ⊆ N.family ∧
      (⟨1, TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ N.family ∧
      (⟨1, TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ N.family ∧
      FixedFieldOutput.Reduces .nativeX N L := by
  let M := tagged L directedPair
  have hLM : L.family ⊆ M.family := by rw [tagged_family]; exact Set.subset_insert _ _
  have hpreM : Preprocessed M.family := by
    intro f hf
    rw [tagged_family] at hf
    rcases hf with rfl | hf
    · exact ⟨by decide, directedPair_ne_zero⟩
    · exact hpre f hf
  have htwoM : ¬ CommonOneSided M.family := fun hs => htwo (hs.mono_family hLM)
  have hpair : (⟨2, directedPair⟩ : AnySignature AlgebraicComplex) ∈ M.family := by
    rw [tagged_family]
    exact Set.mem_insert _ _
  obtain ⟨N, hMN, hz, ho, _, _, hNM, _⟩ := directedPair_factorClosure F M hpreM htwoM hpair
  exact ⟨N, hLM.trans hMN, hz, ho, hNM.trans (directedPair_access_of_complementaryE P L hE)⟩

/-- Actual #P-hardness of the whole original language. The proof does not apply
a singleton EO classification to a non-EO ambient language. -/
theorem complementaryE_hard (P : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (L : Language)
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hnot : ¬ Tract (kImage L))
    (hE : (⟨4, complementaryE⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨N, hLN, hz, _, hNL⟩ := complementaryE_supplies_pins P F L hpre htwo hE
  rcases U.unary_3_4 N (TensorDecomposition.literalPin false)
    (TensorDecomposition.literalPin_ne_zero false) hz with ht | hh
  · exact False.elim (hnot (ht.mono_family (familyAction_mono sourceKBasis hLN)))
  · exact hh.transport hNL


end Paper2.SourceFaithful.RelativeEO
