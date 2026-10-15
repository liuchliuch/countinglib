import Paper2.SourceFaithful.GadgetAugmentation
import Paper2.SourceFaithful.PointMass
import Paper2.ChargeBridgeReduction

/-! Canonical-coordinate machine adapters for the already proved literal charge
networks. No old strict-root hardness or reduction is converted by assumption. -/
namespace Paper2.SourceFaithful.ChargeBridge
open Tractable ExactInput Paper2.ChargeBridge

/-- Lemma 4.1's two actual reductions, retaining exactly the advertised new
members. The source gcd agrees with deletion of its zero element. -/
theorem literal_charge_bridge
    (PD : Paper1DirectGadgetAccepted) (PF : Paper1FactorClosureAccepted)
    (PR : Paper1RestrictionAccepted) (L : Language) (hL : Preprocessed L.family)
    (heven : ∀ i : Fin L.count, Even (L.arity i.val))
    (hpos : ∃ i, ∃ x : Fin (L.arity i.val) → Bool, L.signature i x ≠ 0 ∧ 0 < halfCharge x)
    (hneg : ∃ i, ∃ x : Fin (L.arity i.val) → Bool, L.signature i x ≠ 0 ∧ halfCharge x < 0) :
    let d := languageGcd L
    0 < d ∧ (∀ i : Fin L.count, Tensor.HalfChargeDivisible (L.signature i) d) ∧
      ((∃ f : Signature AlgebraicComplex (2 * d), IsMountain f ∧
          ∃ M : Language, M.family = insert (⟨2 * d, f⟩ : AnySignature AlgebraicComplex) L.family ∧
            FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M) ∨
        ∃ M : Language,
          M.family = insert (⟨1, TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex)
            (insert (⟨1, TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) L.family) ∧
          FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M) := by
  classical
  let d := (supportedCharges (fun i : Fin L.count => L.arity i.val) L.signature).gcd Int.natAbs
  obtain ⟨hd, hout⟩ := finite_family_mountain_or_point_mass_networks
    (fun i : Fin L.count => L.arity i.val) L.signature (by norm_num) heven hpos hneg
  change 0 < d at hd
  refine ⟨hd, fun i => input_charge_divisible _ _ i, ?_⟩
  rcases hout with ⟨f, hmount, G, hU, hX, hG⟩ | ⟨p, q, hp, hq, ⟨GP, hUP, hXP, hGP⟩, ⟨GN, hUN, hXN, hGN⟩⟩
  · left
    exact ⟨f, hmount, PD.adjoin_equivalence PR L f ⟨G, hU, hX, 1, one_ne_zero, by simpa using hG⟩⟩
  · right
    have hP : NativeNetworkRealizesUpTo L.family (pointMass true (2*d) p) :=
      ⟨GP, hUP, hXP, 1, one_ne_zero, by simpa [d, languageGcd] using hGP⟩
    have hN : NativeNetworkRealizesUpTo L.family (pointMass false (2*d) q) :=
      ⟨GN, hUN, hXN, 1, one_ne_zero, by simpa [d, languageGcd] using hGN⟩
    obtain ⟨A, hA, hAL⟩ := PD.adjoin_pair L _ _ hN hP
    have hLA : L.family ⊆ A.family := by
      rw [hA]
      exact Set.Subset.trans (Set.subset_insert _ _) (Set.subset_insert _ _)
    have hpreA : Preprocessed A.family := by
      rw [hA]
      exact preprocessed_insert (preprocessed_insert hL (by omega) (pointMass_ne_zero true _ p hp))
        (by omega) (pointMass_ne_zero false _ q hq)
    have htwoA : ¬ CommonOneSided A.family := by
      intro h
      apply not_commonOneSided_of_signs L heven hpos hneg
      rcases h with h | h
      · exact Or.inl (fun g hg => h g (hLA hg))
      · exact Or.inr (fun g hg => h g (hLA hg))
    obtain ⟨B, hAB, hzero, hone, _, _, hBA, _⟩ :=
      pointMass_pair_factorClosure PF A hpreA htwoA (by omega : 0 < 2*d) (by omega : 0 < 2*d)
        q p hq hp (by rw [hA]; exact Or.inl rfl) (by rw [hA]; exact Or.inr (Or.inl rfl))
    obtain ⟨M, hM⟩ := Language.coverage_family _
      ((L.family_finite.insert ⟨1, TensorDecomposition.literalPin true⟩).insert
        ⟨1, TensorDecomposition.literalPin false⟩)
    refine ⟨M, hM, ?_, PR.restriction_2_5 L M ?_⟩
    · apply (PR.restriction_2_5 M B ?_).trans (hBA.trans hAL)
      intro g hg
      rw [hM] at hg
      rcases hg with rfl | rfl | hg
      · exact hzero
      · exact hone
      · exact hAB (hLA hg)
    · rw [hM]
      exact Set.Subset.trans (Set.subset_insert _ _) (Set.subset_insert _ _)

/-- The unary alternative completes the original nontractable language, using
actual reductions in both directions and the source's literal unary exit. -/
theorem nontractable_charge_bridge
    (PD : Paper1DirectGadgetAccepted) (PF : Paper1FactorClosureAccepted)
    (PR : Paper1RestrictionAccepted) (PU : Paper1UnaryAccepted)
    (L : Language) (hL : Preprocessed L.family)
    (heven : ∀ i : Fin L.count, Even (L.arity i.val))
    (hpos : ∃ i, ∃ x : Fin (L.arity i.val) → Bool, L.signature i x ≠ 0 ∧ 0 < halfCharge x)
    (hneg : ∃ i, ∃ x : Fin (L.arity i.val) → Bool, L.signature i x ≠ 0 ∧ halfCharge x < 0)
    (hnot : ¬ Tract (kImage L)) :
    let d := languageGcd L
    0 < d ∧ (∀ i : Fin L.count, Tensor.HalfChargeDivisible (L.signature i) d) ∧
      ((∃ f : Signature AlgebraicComplex (2 * d), IsMountain f ∧
          ∃ M : Language, M.family = insert (⟨2 * d, f⟩ : AnySignature AlgebraicComplex) L.family ∧
            FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M) ∨
        FixedFieldOutput.SharpPHard .nativeX L) := by
  obtain ⟨hd, hdiv, hm | ⟨M, hM, hML, hLM⟩⟩ :=
    literal_charge_bridge PD PF PR L hL heven hpos hneg
  · exact ⟨hd, hdiv, Or.inl hm⟩
  · refine ⟨hd, hdiv, Or.inr ?_⟩
    have hu : (⟨1, TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ M.family := by
      rw [hM]
      exact Or.inl rfl
    rcases PU.unary_3_4 M _ (TensorDecomposition.literalPin_ne_zero false) hu with ht | hh
    · exfalso
      apply hnot
      apply ht.mono_family
      apply familyAction_mono sourceKBasis
      rw [hM]
      exact Set.Subset.trans (Set.subset_insert _ _) (Set.subset_insert _ _)
    · exact hh.transport hML

end Paper2.SourceFaithful.ChargeBridge
