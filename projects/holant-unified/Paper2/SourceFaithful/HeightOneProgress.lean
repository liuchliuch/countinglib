import Paper2.SourceFaithful.HeightOneLedger

/-! Every concrete retained raw-coordinate stage uses the source's fixed
number-field potential. The group cardinality is the actual all-realizable
projective group, and the minimum arity is realized by a retained prime. -/
namespace Paper2.SourceFaithful.HeightOne
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Tractable ExactInput
open Paper2.HeightOne Paper2.HeightOne.PhaseCards
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup

structure PrimeStage (L : Language) extends RawStage L where
  minArity : ℕ
  least : LeastPrimeArity language.family minArity

def PrimeStage.progress {L : Language} (S : PrimeStage L) : ProgressState :=
  ⟨(actualClasses S.language.family).ncard, S.minArity, S.least.ge_three⟩

def originalBound (L : Language) : ℕ := uniformProjectiveBound (Module.finrank ℚ (originalField L))

def PrimeStage.measure {L : Language} (S : PrimeStage L) : ℕ := potential (originalBound L) S.progress

/-- A genuine group inclusion and/or arity decrease is sufficient; the uniform
bound of the successor is proved from its actual raw coefficient ledger. -/
theorem PrimeStage.measure_decreases (P : GroupSplit.Paper1Accepted)
    {L : Language} (S T : PrimeStage L)
    (hgroup : actualClasses S.language.family ⊆ actualClasses T.language.family)
    (harity : T.minArity ≤ S.minArity)
    (hstrict : actualClasses S.language.family ⊂ actualClasses T.language.family ∨
      T.minArity < S.minArity) : T.measure < S.measure := by
  apply potential_decreases
  refine ⟨Set.ncard_le_ncard hgroup (T.classes_finite P), T.card_le_bound P, harity, ?_⟩
  rcases hstrict with hgroup | harity
  · exact Or.inl (Set.ncard_lt_ncard hgroup (T.classes_finite P))
  · exact Or.inr harity

/-- Global normalization changes neither actual finite-group cardinality nor
least prime arity. Thus strict comparisons made in normalized coordinates
are exactly the strict comparisons used by the raw fixed-field potential. -/
theorem strict_progress_of_normalized_saturation
    (P : GroupSplit.Paper1Accepted) {L : Language} (S T : PrimeStage L)
    (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (M B : Language) (hM : M.family = familyAction D S.language.family)
    (hB : T.language.family = familyAction D.symm B.family)
    (hgroup : actualClasses M.family ⊆ actualClasses B.family)
    (hfiniteB : (actualClasses B.family).Finite)
    (harity : T.minArity ≤ S.minArity)
    (hstrict : actualClasses M.family ⊂ actualClasses B.family ∨
      T.minArity < S.minArity) : T.measure < S.measure := by
  have hcardM : (actualClasses M.family).ncard = (actualClasses S.language.family).ncard := by
    rw [hM]
    exact classes_ncard_diagonal _ D a b hD ha hb
  have hcardB : (actualClasses T.language.family).ncard = (actualClasses B.family).ncard := by
    rw [hB]
    exact classes_ncard_diagonal _ D.symm a⁻¹ b⁻¹
      (inverse_diagonal D a b hD ha hb) (inv_ne_zero ha) (inv_ne_zero hb)
  apply potential_decreases
  refine ⟨?_, T.card_le_bound P, harity, ?_⟩
  · change (actualClasses S.language.family).ncard ≤ (actualClasses T.language.family).ncard
    rw [← hcardM, hcardB]
    exact Set.ncard_le_ncard hgroup hfiniteB
  · rcases hstrict with hstrict | hstrict
    · left
      change (actualClasses S.language.family).ncard < (actualClasses T.language.family).ncard
      rw [← hcardM, hcardB]
      exact Set.ncard_lt_ncard hstrict hfiniteB
    · exact Or.inr hstrict


lemma not_commonOneSided_action {F : SignatureFamily AlgebraicComplex}
    (D : InvertibleKernel) (hD : XConformal D) (hF : ¬ CommonOneSided F) :
    ¬ CommonOneSided (familyAction D F) := by
  intro h
  obtain ⟨opposite,a,b,ha,hb,hshape⟩ := Conformal.hasShape_of_xConformal hD.symm
  have hh := Conformal.shape_commonOneSided hshape ha hb h
  rw [Conformal.familyAction_symm_action] at hh
  exact hF hh

lemma safe_classes_finite (P : GroupSplit.Paper1Accepted) (L : Language)
    (hsafe : AllBinariesSafe L.family) (hbinary : ∃ B : AMat, ActualNonsingular L.family B) :
    (actualClasses L.family).Finite := by
  have hne : (actualTransfers L.family).Nonempty := by
    obtain ⟨B,hB⟩ := hbinary
    exact ⟨transfer B,B,hB,1,one_ne_zero,by simp⟩
  have htor : ∀ B, ActualNonsingular L.family B → ProjectivelyFinite (transfer B) := by
    intro B hB
    apply (hsafe B hB.1 ?_).2
    intro hz
    exact hB.2 (by rw [hz, Matrix.det_zero])
  exact finite_actualClasses P L.family L.family_finite hne htor

/-- A real normalized card saturation either terminates, strictly decreases
the actual fixed-field potential after inverse normalization, or reaches a
stable processed family with exactly the same group and least prime arity.
No successful successor operation is supplied as an assumption. -/
theorem normalized_saturation_progress
    (P1 : GroupSplit.Paper1Accepted)
    (PG : Paper1DirectGadgetAccepted) (PR : Paper1RestrictionAccepted)
    (PF : Paper1FactorClosureAccepted) (PU : Paper1UnaryAccepted)
    (PI : Paper1BinaryInterpolationAccepted) (PO : Paper1OddAccepted)
    (PN : Paper1NormalizationAccepted) {L : Language} (S : PrimeStage L)
    (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hconf : XConformal D) (M : Language)
    (hM : M.family = familyAction D S.language.family)
    (hML : FixedFieldOutput.Reduces .nativeX M S.language)
    (hLM : FixedFieldOutput.Reduces .nativeX S.language M)
    (menu : BinaryMenu M.family) :
    Terminal L ∨ (∃ T : PrimeStage L, T.measure < S.measure) ∨
      ∃ B : Language, SaturatedStage M B menu (originalField L) D ∧
        LeastPrimeArity B.family S.minArity ∧ actualClasses B.family = actualClasses M.family := by
  have hpreM : Preprocessed M.family := by
    rw [hM]
    exact Conformal.preprocessed_familyAction D S.retained.preprocessed
  have htwoM : ¬ CommonOneSided M.family := by
    rw [hM]
    exact not_commonOneSided_action D hconf S.retained.notOneSided
  have hfacM : FactorClosed M.family := by
    rw [hM]
    exact factorClosed_action S.language.family D S.factorClosed
  have hminM : LeastPrimeArity M.family S.minArity := by
    rw [hM]
    exact Paper2.SourceFaithful.HeightOne.LeastPrimeArity.action S.least D
  have hfieldM : ∀ f ∈ M.family, PullbackOver (originalField L) D f := by
    rintro f hf
    rw [hM] at hf
    obtain ⟨g,hg,rfl⟩ := hf
    simpa only [PullbackOver, InvertibleKernel.symm_action_action] using S.field g hg
  rcases card_saturation_trichotomy PG PR PF PU PI PO M hpreM htwoM hfacM
    menu (originalField L) D a b hD ha hb hfieldM S.minArity hminM with ht | hnext
  · left
    rcases ht with ht | hh
    · apply S.terminal
      left
      apply (xConformal_tract_iff hconf S.language.family).mpr
      simpa only [kImage, hM] using ht
    · exact Or.inr (hh.transport (hML.trans S.retained.backward))
  · obtain ⟨B,ν,hB,hminB,hν,hgroup,hstrict | ⟨heq,hνeq⟩⟩ := hnext
    · right
      left
      obtain ⟨T,hT⟩ := S.toRawStage.extend_saturated P1 PR PN D a b hD ha hb hconf
        M B hM hML hLM hB.retained hB.factorClosed hB.field hB.safe
      have hminT : LeastPrimeArity T.language.family ν := by
        rw [hT]
        exact Paper2.SourceFaithful.HeightOne.LeastPrimeArity.action hminB D.symm
      let U : PrimeStage L := ⟨T,ν,hminT⟩
      refine ⟨U, strict_progress_of_normalized_saturation P1 S U D a b hD ha hb
        M B hM hT hgroup ?_ hν hstrict⟩
      have hbinaryM : ∃ C : AMat, ActualNonsingular M.family C := by
        rw [hM]
        exact actual_binary_diagonal S.binary D a b hD ha hb
      have hbinaryB : ∃ C : AMat, ActualNonsingular B.family C := by
        obtain ⟨C,hC⟩ := hbinaryM
        exact ⟨C,networkRealizable_mono hB.retained.subset hC.1,hC.2⟩
      exact safe_classes_finite P1 B hB.safe hbinaryB
    · right
      right
      subst ν
      exact ⟨B,hB,hminB,heq⟩

end
end Paper2.SourceFaithful.HeightOne

