import Paper2.Paper1ProvedOddUnaryIsotropicStage
import Paper2.Paper1ProvedOddUnaryTwoWordExtraction
import Paper2.Paper1ProvedOddUnaryGeneralizedEqualitySmall

/-! The retained independent-isotropic language has both literal unit pins
and a member with more than one occupied weight. Physical pin and X-loop
descent therefore extracts an actual weighted generalized equality. The two
small arities have proved native exits; larger arities are recorded with the
unchanged retained language and its canonical fixed-field reduction. -/
namespace Paper2.Paper1Proved.OddUnary.IsotropicGeneralizedEqualityStage
open Paper2.Tractable Paper2.ExactInput Paper2.ExactInput.Computation Paper2.Synthesis
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A true ordinary ternary source on the K-image of the retained native
language, together with its actual canonical route to the original input. -/
structure RetainedTernarySource (L : Language) : Type 1 where
  retained : IsotropicStage.Retained L
  source : TernarySource (kLanguage retained.language)

/-- The remaining arity-at-least-three source is an exact native-X network
over the finite retained language. Its pins and reductions are supplied by
`retained`, rather than inferred from arbitrary oracle reducibility. -/
structure GeneralizedEqualitySource (L : Language) : Type 1 where
  retained : IsotropicStage.Retained L
  arity : ℕ
  arityAtLeastThree : 3 ≤ arity
  first : AlgebraicComplex
  second : AlgebraicComplex
  firstNonzero : first ≠ 0
  secondNonzero : second ≠ 0
  graph : NetworkRealizable retained.language.family
    (RelativeEO.generalizedEquality (n := arity) first second)

theorem RetainedTernarySource.transfer_hard {L : Language} (S : RetainedTernarySource L)
    (h : FixedFieldOutput.SharpPHard .ordinary (kLanguage S.retained.language)) :
    FixedFieldOutput.SharpPHard .ordinary L :=
  S.retained.transfer_hard ((FixedFieldOutput.native_hard_iff S.retained.language).mpr h)

theorem GeneralizedEqualitySource.transfer_hard {L : Language} (S : GeneralizedEqualitySource L)
    (h : FixedFieldOutput.SharpPHard .nativeX S.retained.language) :
    FixedFieldOutput.SharpPHard .ordinary L :=
  S.retained.transfer_hard h

/-- The non-single-layer witness is a literal original-label corolla before
the proved physical least-gap descent is applied. -/
theorem extract {L : Language} (S : IsotropicStage.Retained L) :
    ∃ k : ℕ, ∃ a b : AlgebraicComplex, 0 < k ∧ a ≠ 0 ∧ b ≠ 0 ∧
      NetworkRealizable S.language.family (RelativeEO.generalizedEquality (n := k) a b) := by
  classical
  obtain ⟨f,hf,hmulti⟩ : ∃ f ∈ S.language.family, ¬ ∃ d, Signature.SingleLayer f.2 d := by
    by_contra hn
    apply S.nonlayer
    intro f hf
    by_contra hmulti
    exact hn ⟨f,hf,hmulti⟩
  have hgraph : NetworkRealizable S.language.family f.2 := by
    refine ⟨f.1,Network.corolla f.2,Equiv.refl _,?_,?_,?_⟩
    · intro v
      exact hf
    · intro e
      exact Fin.elim0 e
    · simpa only [Tensor.reindex_refl] using Network.denote_corolla f.2
  exact TwoWordExtraction.generalizedEquality_of_not_singleLayer S.language.family
    f.2 hgraph S.pinZero S.pinOne hmulti

theorem retained_hard_or_ternary_or_generalizedEquality
    (P : SourceFaithful.Paper1Accepted)
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (F : SourceFaithful.Paper1FactorClosureAccepted)
    (N : SourceFaithful.Paper1NormalizationAccepted)
    {L : Language} (S : IsotropicStage.Retained L) :
    FixedFieldOutput.SharpPHard .ordinary L ∨
      Nonempty (RetainedTernarySource L) ∨ Nonempty (GeneralizedEqualitySource L) := by
  obtain ⟨k,a,b,hk,ha,hb,hgraph⟩ := extract S
  by_cases hk1 : k = 1
  · subst k
    rcases NativeExit.nonisotropic_hard_or_ternary P G R F N S.language S.nontractable
        (RelativeEO.generalizedEquality (n := 1) a b) hgraph
        (GeneralizedEqualitySmall.one_norm_ne_zero a b ha hb) with hh | ht
    · exact Or.inl (S.transfer_hard hh)
    · exact Or.inr (Or.inl (ht.elim (fun t => ⟨⟨S,t⟩⟩)))
  · by_cases hk2 : k = 2
    · subst k
      exact Or.inl (S.transfer_hard (WeightedEquality.realizable_hard P G N
        S.language S.preprocessed S.nontractable _
        (GeneralizedEqualitySmall.two_weightedEquality a b ha hb) hgraph))
    · exact Or.inr (Or.inr ⟨⟨S,k,by omega,a,b,ha,hb,hgraph⟩⟩)

/-- The independent-isotropic pair now reaches either original-language
hardness, a true ternary source, or an actual finite generalized equality
source. No generalized-equality classification is assumed. -/
theorem hard_or_ternary_or_generalizedEquality
    (P : SourceFaithful.Paper1Accepted)
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (F : SourceFaithful.Paper1FactorClosureAccepted)
    (E : SourceFaithful.Paper1EOAccepted)
    (N : SourceFaithful.Paper1NormalizationAccepted)
    (L : Language) (hp : Preprocessed L.family) (hnot : ¬ Tract L.family)
    (pair : IsotropicPairSource L) :
    FixedFieldOutput.SharpPHard .ordinary L ∨
      Nonempty (RetainedTernarySource L) ∨ Nonempty (GeneralizedEqualitySource L) := by
  rcases IsotropicStage.hard_or_retained G R F E L hp hnot pair with hh | hs
  · exact Or.inl hh
  · exact hs.elim (retained_hard_or_ternary_or_generalizedEquality P G R F N)

end
end Paper2.Paper1Proved.OddUnary.IsotropicGeneralizedEqualityStage

