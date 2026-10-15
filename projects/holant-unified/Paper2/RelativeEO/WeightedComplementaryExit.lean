import Paper2.RelativeEO.ComplementaryExit
import Paper2.RelativeEO.WeightedComplementaryNormalization

/-! Full weighted, arbitrary ordered support version of Paper 2 Lemma 3.8.
The only accepted inputs are the exact cited Paper 1 reduction and unary
results. All new complementary, copying, and factor identities are proved. -/
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.Problem

lemma complementaryE_ne_zero : complementaryE ≠ 0 := by
  intro hz
  have h := congrFun hz (quadWord false false true true)
  change (1 : AlgebraicComplex) = 0 at h
  exact one_ne_zero h

lemma bothChargeSigns_not_oneSided {F : SignatureFamily AlgebraicComplex}
    (h : BothChargeSigns F) : ¬ CommonOneSided F := by
  obtain ⟨⟨f, hf, x, hx, hneg⟩, ⟨g, hg, y, hy, hpos⟩⟩ := h
  intro hs
  rcases hs with hs | hs
  · exact (not_le_of_gt hneg) (hs f hf x hx)
  · exact (not_le_of_gt hpos) (hs g hg y hy)

/-- Both copies use the original signature, with the normalization pq explicitly
recorded in the true native-X network. -/
theorem complementaryTable_realized {F : SignatureFamily AlgebraicComplex}
    (s : Fin 4 → Bool) (hs : weight s = 2) (p q : AlgebraicComplex)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hD : (⟨4, complementaryTable s p q⟩ : AnySignature AlgebraicComplex) ∈ F) :
    NativeNetworkRealizesUpTo F complementaryE := by
  obtain ⟨N, hu, hx, hd⟩ := complementaryTable_network s hs p q hD
  exact ⟨N, hu, hx, p * q, mul_ne_zero hp hq, hd⟩

/-- Paper 2 Lemma 3.8, with its equivalent augmentation made literal: both unit
pins are actual members of a finite exact language reducing to the original L.
The proof needs the charge assumption, but not nontractability until hardness. -/
theorem complementary_supplies_pins (G : Paper1DirectGadgetAccepted)
    (P : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted) (L : Language)
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (s : Fin 4 → Bool) (hs : weight s = 2) (p q : AlgebraicComplex)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hD : (⟨4, complementaryTable s p q⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ N : Language, L.family ⊆ N.family ∧
      (⟨1, TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ N.family ∧
      (⟨1, TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ N.family ∧
      Reduces .nativeX N L := by
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
    SharpPHard .nativeX L := by
  obtain ⟨N, hLN, hz, _, hNL⟩ := complementary_supplies_pins G P F L hpre
    (bothChargeSigns_not_oneSided hboth) s hs p q hp hq hD
  rcases U.unary_3_4 N (TensorDecomposition.literalPin false)
    (TensorDecomposition.literalPin_ne_zero false) hz with ht | hh
  · exact False.elim (hnot (ht.mono_family (familyAction_mono sourceKBasis hLN)))
  · exact hh.transport_unconditional hNL

end Paper2.RelativeEO
