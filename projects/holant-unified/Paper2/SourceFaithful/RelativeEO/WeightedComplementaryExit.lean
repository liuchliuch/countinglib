import Paper2.RelativeEO.WeightedComplementaryExit
import Paper2.SourceFaithful.RelativeEO.ComplementaryExit

/-! Canonical fixed-field answer version of the proved local construction.
The pure signatures/networks are unchanged. Machine reductions are proved again
from the separately named source-exact records; no output-code conversion or
old strict-root classification is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.SourceFaithful.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.RelativeEO

theorem complementary_supplies_pins (G : Paper1DirectGadgetAccepted)
    (P : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted) (L : Language)
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (s : Fin 4 → Bool) (hs : weight s = 2) (p q : AlgebraicComplex)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hD : (⟨4, complementaryTable s p q⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ N : Language, L.family ⊆ N.family ∧
      (⟨1, TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ N.family ∧
      (⟨1, TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ N.family ∧
      FixedFieldOutput.Reduces .nativeX N L := by
  obtain ⟨M, hM, hML⟩ := G.adjoin L complementaryE
    (complementaryTable_realized s hs p q hp hq hD)
  have hLM : L.family ⊆ M.family := by rw [hM]; exact Set.subset_insert _ _
  have hpreM : Preprocessed M.family := by
    intro f hf
    rw [hM] at hf
    rcases hf with rfl | hf
    · exact ⟨by decide, complementaryE_ne_zero⟩
    · exact hpre f hf
  have htwoM : ¬ CommonOneSided M.family := fun hh => htwo (hh.mono_family hLM)
  have hE : (⟨4, complementaryE⟩ : AnySignature AlgebraicComplex) ∈ M.family := by
    rw [hM]
    exact Set.mem_insert _ _
  obtain ⟨N, hMN, hz, ho, hNM⟩ := complementaryE_supplies_pins P F M hpreM htwoM hE
  exact ⟨N, hLM.trans hMN, hz, ho, hNM.trans hML⟩

/-- The actual ambient-language hardness exit consumed by both local EO and ARS
proofs. It neither assumes nor invokes their still-open general alternatives. -/
theorem complementary_hard (G : Paper1DirectGadgetAccepted)
    (P : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (L : Language)
    (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L))
    (s : Fin 4 → Bool) (hs : weight s = 2) (p q : AlgebraicComplex)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hD : (⟨4, complementaryTable s p q⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨N, hLN, hz, _, hNL⟩ := complementary_supplies_pins G P F L hpre
    (bothChargeSigns_not_oneSided hboth) s hs p q hp hq hD
  rcases U.unary_3_4 N (TensorDecomposition.literalPin false)
    (TensorDecomposition.literalPin_ne_zero false) hz with ht | hh
  · exact False.elim (hnot (ht.mono_family (familyAction_mono sourceKBasis hLN)))
  · exact hh.transport hNL


end Paper2.SourceFaithful.RelativeEO
