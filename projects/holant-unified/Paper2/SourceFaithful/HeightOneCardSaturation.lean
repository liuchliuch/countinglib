import Paper2.SourceFaithful.HeightOneSaturation
import Paper2.SourceFaithful.HeightOneUnsafeBinary
import Paper2.SourceFaithful.Synthesis.InitialBranches
import Paper2.HeightOne.CardSaturation

/-! Source Lemma 5.8 with canonical fixed-field oracle answers. Actual complete
projective groups, minimal nonbinary arity and the fixed original coefficient
field all remain explicit; no terminal or strict update is assumed. -/
namespace Paper2.SourceFaithful.HeightOne
noncomputable section
open Tractable ExactInput
open Paper2.HeightOne Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup
open Paper2.HeightOne.PhaseCards

def Terminal (L : Language) : Prop := Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L

lemma terminal_of_retained {L B : Language} (hB : SourceRetainedExtension L B) (ht : Terminal B) :
    Terminal L := by
  rcases ht with ht | hh
  · exact Or.inl (ht.mono_family (familyAction_mono sourceKBasis hB.subset))
  · exact Or.inr (hh.transport hB.backward)

/-- The exact invariants retained at a nonterminal same-coordinate stage.
The matrix and the frozen field are parameters of both ends of the step. -/
structure SaturatedStage (L B : Language) (M : BinaryMenu L.family)
    (E : Subfield AlgebraicComplex) (A : InvertibleKernel) : Prop where
  retained : SourceRetainedExtension L B
  factorClosed : FactorClosed B.family
  processed : ∀ f ∈ B.family, M.Processed f B
  field : ∀ f ∈ B.family, PullbackOver E A f
  even : ∀ f ∈ B.family, Even f.1
  safe : AllBinariesSafe B.family

/-- Literal source Lemma 5.8 for any fixed finite menu of actual representatives.
When used with the complete menu below, all classes of the original complete
safe group occur. The third outcome has exactly the same group and minimum
prime arity; the second has a true strict comparison and both weak comparisons. -/
theorem card_saturation_trichotomy
    (PG : Paper2.SourceFaithful.Paper1DirectGadgetAccepted) (PR : Paper2.SourceFaithful.Paper1RestrictionAccepted)
    (PF : Paper2.SourceFaithful.Paper1FactorClosureAccepted) (PU : Paper2.SourceFaithful.Paper1UnaryAccepted)
    (PI : Paper2.SourceFaithful.Paper1BinaryInterpolationAccepted) (PO : Paper2.SourceFaithful.Paper1OddAccepted)
    (L : Language) (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hfac : FactorClosed L.family) (M : BinaryMenu L.family)
    (E : Subfield AlgebraicComplex) (A : InvertibleKernel)
    (a b : AlgebraicComplex) (hA : A.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfield : ∀ f ∈ L.family, PullbackOver E A f)
    (ν : ℕ) (hmin : LeastPrimeArity L.family ν) :
    Terminal L ∨ ∃ (B : Language) (ν' : ℕ), SaturatedStage L B M E A ∧
      LeastPrimeArity B.family ν' ∧ ν' ≤ ν ∧
      actualClasses L.family ⊆ actualClasses B.family ∧
      ((actualClasses L.family ⊂ actualClasses B.family ∨ ν' < ν) ∨
        (actualClasses B.family = actualClasses L.family ∧ ν' = ν)) := by
  classical
  obtain ⟨B, hB, hfacB, hprocessed, hfieldB⟩ :=
    M.source_finite_factor_closed_saturation_pullback PG PR PF L hpre htwo
      (Set.Subset.refl _) hfac E A a b hA ha hb hfield
  by_cases hodd : ∃ f ∈ B.family, Odd f.1 ∧ f.2 ≠ 0
  · left
    exact terminal_of_retained hB (Paper2.SourceFaithful.Synthesis.odd_classification_preprocessed PO B hB.preprocessed hodd)
  have heven : ∀ f ∈ B.family, Even f.1 := by
    intro f hf
    rcases Nat.even_or_odd f.1 with he | ho
    · exact he
    · exact False.elim (hodd ⟨f, hf, ho, (hB.preprocessed f hf).2⟩)
  by_cases hsafe : AllBinariesSafe B.family
  · right
    have hnonbin : HasNonbinaryPrime B.family := by
      obtain ⟨f, hf, hp, rfl, hn⟩ := hmin.1
      exact ⟨f, hB.subset hf, hp, hn⟩
    obtain ⟨ν', hminB⟩ := exists_leastPrimeArity hnonbin
    have hν := hmin.mono hminB hB.subset
    have hgroup := actualClasses_mono hB.subset
    refine ⟨B, ν', ⟨hB, hfacB, hprocessed, hfieldB, heven, hsafe⟩, hminB, hν, hgroup, ?_⟩
    by_cases heq : actualClasses B.family = actualClasses L.family
    · by_cases heqn : ν' = ν
      · exact Or.inr ⟨heq, heqn⟩
      · exact Or.inl (Or.inr (lt_of_le_of_ne hν heqn))
    · exact Or.inl (Or.inl (Set.ssubset_iff_subset_ne.mpr ⟨hgroup, Ne.symm heq⟩))
  · left
    exact terminal_of_retained hB (unsafe_actual_binary_classification PG PR PF PU PI B
      hB.preprocessed (signs_of_not_commonOneSided hB.notOneSided) hsafe)

/-- The complete menu is proved to exist from the actual safe group, including
all actual classes rather than only the binaries currently literal in L. -/
theorem complete_card_saturation
    (P1 : GroupSplit.Paper1Accepted)
    (PG : Paper2.SourceFaithful.Paper1DirectGadgetAccepted) (PR : Paper2.SourceFaithful.Paper1RestrictionAccepted)
    (PF : Paper2.SourceFaithful.Paper1FactorClosureAccepted) (PU : Paper2.SourceFaithful.Paper1UnaryAccepted)
    (PI : Paper2.SourceFaithful.Paper1BinaryInterpolationAccepted) (PO : Paper2.SourceFaithful.Paper1OddAccepted)
    (L : Language) (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hfac : FactorClosed L.family) (hsafe : AllBinariesSafe L.family)
    (hbinary : ∃ B : AMat, ActualNonsingular L.family B)
    (E : Subfield AlgebraicComplex) (A : InvertibleKernel)
    (a b : AlgebraicComplex) (hA : A.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfield : ∀ f ∈ L.family, PullbackOver E A f) :
    Terminal L ∨ ∃ (M : BinaryMenu L.family) (ν : ℕ),
      (∀ q ∈ actualClasses L.family, ∃ i,
        projectiveClass (transfer (M.binary i)) = pglToProjectiveClass q) ∧
      LeastPrimeArity L.family ν ∧
      ∃ (B : Language) (ν' : ℕ), SaturatedStage L B M E A ∧
        LeastPrimeArity B.family ν' ∧ ν' ≤ ν ∧
        actualClasses L.family ⊆ actualClasses B.family ∧
        ((actualClasses L.family ⊂ actualClasses B.family ∨ ν' < ν) ∨
          (actualClasses B.family = actualClasses L.family ∧ ν' = ν)) := by
  classical
  by_cases hnonbin : HasNonbinaryPrime L.family
  · obtain ⟨ν, hmin⟩ := exists_leastPrimeArity hnonbin
    obtain ⟨B, hB⟩ := hbinary
    have hne : (actualTransfers L.family).Nonempty :=
      ⟨transfer B, B, hB, 1, one_ne_zero, by simp⟩
    have htorsion : ∀ C, ActualNonsingular L.family C → ProjectivelyFinite (transfer C) := by
      intro C hC
      apply (hsafe C hC.1 ?_).2
      intro hz
      exact hC.2 (by rw [hz, Matrix.det_zero])
    have hfinite := finite_actualClasses P1 L.family L.family_finite hne htorsion
    obtain ⟨M, hM⟩ := complete_binaryMenu hfinite
    rcases card_saturation_trichotomy PG PR PF PU PI PO L hpre htwo hfac M E A a b hA ha hb
      hfield ν hmin with ht | hnext
    · exact Or.inl ht
    · exact Or.inr ⟨M, ν, hM, hmin, hnext⟩
  · exact Or.inl (Or.inl (tract_of_no_nonbinary L hfac hnonbin))

end
end Paper2.SourceFaithful.HeightOne

