import Paper2.SourceFaithful.HeightOneCardSaturation
import Paper2.HeightOne.PhaseCards.FieldGroup
import Paper2.HeightOne.PhaseCards.OrientedMenu
import Paper2.HeightOne.TensorPrimeTools
import Paper2.ExactInput.FixedFieldBridge

/-! Concrete fixed-field bookkeeping for the height-one strict iteration.
After each normalized saturation its exact inverse normalization returns to
the preceding raw coordinates. Thus every continuing language retains the
original resources and uses one original number field projectively. -/
namespace Paper2.SourceFaithful.HeightOne
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Tractable ExactInput
open Paper2.HeightOne Paper2.HeightOne.PhaseCards
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup

/-- The field is selected once from the literal original coefficient table. -/
def originalField (L : Language) : Subfield AlgebraicComplex := L.coefficientField.toSubfield

instance originalField_numberField (L : Language) : NumberField (originalField L) where
  to_charZero := inferInstance
  to_finiteDimensional := by
    change FiniteDimensional ℚ L.coefficientField
    infer_instance

lemma original_family_over_field (L : Language) :
    ∀ f ∈ L.family, ProjectivelyOver (originalField L) f.2 := by
  rintro f ⟨i, rfl⟩
  exact ⟨1, one_ne_zero, fun x => by
    simpa only [one_mul, originalField, IntermediateField.mem_toSubfield] using L.signature_mem_field i x⟩

lemma factorClosed_action (F : SignatureFamily AlgebraicComplex) (B : InvertibleKernel)
    (hF : FactorClosed F) : FactorClosed (familyAction B F) := by
  rintro f ⟨g, hg, rfl⟩
  obtain ⟨Q, he, hpos, hprime, hmem⟩ := hF g hg
  refine ⟨Q.mapAction B.matrix, ?_, hpos, fun i => tensorPrime_action B (hprime i), ?_⟩
  · rw [TensorDecomposition.value_mapAction, he]
    rfl
  · intro i
    exact ⟨⟨Q.arity i, Q.factor i⟩, hmem i, rfl⟩

lemma LeastPrimeArity.action {F : SignatureFamily AlgebraicComplex} {n : ℕ}
    (hF : LeastPrimeArity F n) (B : InvertibleKernel) :
    LeastPrimeArity (familyAction B F) n := by
  constructor
  · obtain ⟨f,hf,hp,he,hn⟩ := hF.1
    exact ⟨⟨f.1,B.action f.2⟩, ⟨f,hf,rfl⟩, tensorPrime_action B hp, he, hn⟩
  · rintro g ⟨f,hf,rfl⟩ hp hn
    exact hF.2 f hf ((tensorPrime_action_iff B f.2).mp hp) hn

lemma classes_ncard_diagonal (F : SignatureFamily AlgebraicComplex)
    (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    (actualClasses (familyAction D F)).ncard = (actualClasses F).ncard := by
  rw [completeClasses_diagonal_transport F D a b hD ha hb]
  exact Set.ncard_image_of_injective _ (MulAut.conj (pglMk _ (basisGL D))).injective

/-- Exact descent to the original field preserves the actual group cardinality.
The descent is through the real injective PGL₂(field) map, not a proxy group. -/
theorem actualClasses_card_le_fixed_field
    (E : Subfield AlgebraicComplex) [NumberField E]
    (F : SignatureFamily AlgebraicComplex) (hfield : ∀ f ∈ F, ProjectivelyOver E f.2)
    (hgroup : ProjectiveMatrixGroup (actualTransfers F)) (hfinite : (actualClasses F).Finite) :
    (actualClasses F).ncard ≤ uniformProjectiveBound (Module.finrank ℚ E) := by
  let H := projectiveSubgroup hgroup
  have hrange : H ≤ (pglMap E.subtype).range := actualClasses_in_subfield_range E hfield
  haveI : Finite H := hfinite.to_subtype
  let e : descendFieldGroup E H ≃ H := Equiv.ofBijective
    (fun q => ⟨pglMap E.subtype q, q.property⟩)
    ⟨fun a b h => Subtype.ext (pglMap_injective E.subtype (congrArg Subtype.val h)),
      by
        intro q
        obtain ⟨r, hr⟩ := hrange q.property
        refine ⟨⟨r, ?_⟩, ?_⟩
        · change pglMap E.subtype r ∈ H
          rw [hr]
          exact q.property
        · exact Subtype.ext hr⟩
  change Nat.card H ≤ _
  rw [← Nat.card_congr e]
  exact card_descendFieldGroup_le E H

/-- A continuing raw stage carries literal original inclusion and genuine
canonical reductions. Its group and minimum prime arity are derived below. -/
structure RawStage (L : Language) where
  language : Language
  retained : SourceRetainedExtension L language
  factorClosed : FactorClosed language.family
  field : ∀ f ∈ language.family, ProjectivelyOver (originalField L) f.2
  safe : AllBinariesSafe language.family
  binary : ∃ B : AMat, ActualNonsingular language.family B

namespace RawStage

lemma group_torsion {L : Language} (S : RawStage L) :
    ∀ B, ActualNonsingular S.language.family B → ProjectivelyFinite (transfer B) := by
  intro B hB
  apply (S.safe B hB.1 ?_).2
  intro hz
  exact hB.2 (by rw [hz, Matrix.det_zero])

lemma transfers_nonempty {L : Language} (S : RawStage L) :
    (actualTransfers S.language.family).Nonempty := by
  obtain ⟨B,hB⟩ := S.binary
  exact ⟨transfer B,B,hB,1,one_ne_zero,by simp⟩

lemma classes_finite (P : GroupSplit.Paper1Accepted) {L : Language} (S : RawStage L) :
    (actualClasses S.language.family).Finite :=
  finite_actualClasses P S.language.family S.language.family_finite S.transfers_nonempty S.group_torsion

lemma card_le_bound (P : GroupSplit.Paper1Accepted) {L : Language} (S : RawStage L) :
    (actualClasses S.language.family).ncard ≤
      uniformProjectiveBound (Module.finrank ℚ (originalField L)) :=
  actualClasses_card_le_fixed_field (originalField L) S.language.family S.field
    (actualTransfers_projectiveMatrixGroup S.language.family S.transfers_nonempty S.group_torsion)
    (S.classes_finite P)

lemma terminal {L : Language} (S : RawStage L) (h : Terminal S.language) : Terminal L :=
  terminal_of_retained S.retained h

end RawStage

/-- Inverse normalization really returns a retained raw-coordinate extension.
The fixed-field condition is precisely the inverse tensor action already
recorded by the normalized saturation. -/
theorem inverse_normalized_retained_stage
    (PR : Paper1RestrictionAccepted) (PN : Paper1NormalizationAccepted)
    (L M B : Language) (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hconf : XConformal D) (hM : M.family = familyAction D L.family)
    (hML : FixedFieldOutput.Reduces .nativeX M L)
    (hLM : FixedFieldOutput.Reduces .nativeX L M)
    (hB : SourceRetainedExtension M B) (hfac : FactorClosed B.family)
    (E : Subfield AlgebraicComplex) (hfield : ∀ f ∈ B.family, PullbackOver E D f) :
    ∃ A : Language, SourceRetainedExtension L A ∧ FactorClosed A.family ∧
      A.family = familyAction D.symm B.family ∧
      (∀ f ∈ A.family, ProjectivelyOver E f.2) ∧
      (actualClasses A.family).ncard = (actualClasses B.family).ncard := by
  obtain ⟨A,hA,hAB,hBA⟩ := PN.normalize B hB.preprocessed D.symm hconf.symm
  have hsub : L.family ⊆ A.family := by
    have hh := familyAction_mono D.symm hB.subset
    rw [hM, Conformal.familyAction_symm_action, ← hA] at hh
    exact hh
  refine ⟨A, ⟨hsub, ?_, ?_, hAB.trans (hB.backward.trans hML),
    hLM.trans (hB.forward.trans hBA)⟩, ?_, hA, ?_, ?_⟩
  · rw [hA]
    exact Conformal.preprocessed_familyAction D.symm hB.preprocessed
  · intro hn
    apply htwo
    rcases hn with hn | hn
    · exact Or.inl (fun f hf => hn f (hsub hf))
    · exact Or.inr (fun f hf => hn f (hsub hf))
  · rw [hA]
    exact factorClosed_action B.family D.symm hfac
  · rintro f hf
    rw [hA] at hf
    obtain ⟨g,hg,rfl⟩ := hf
    exact hfield g hg
  · rw [hA]
    exact classes_ncard_diagonal B.family D.symm a⁻¹ b⁻¹
      (inverse_diagonal D a b hD ha hb) (inv_ne_zero ha) (inv_ne_zero hb)


lemma safe_diagonal (P : GroupSplit.Paper1Accepted) (L : Language)
    (hsafe : AllBinariesSafe L.family) (hbinary : ∃ B : AMat, ActualNonsingular L.family B)
    (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    AllBinariesSafe (familyAction D L.family) := by
  have hne : (actualTransfers L.family).Nonempty := by
    obtain ⟨B,hB⟩ := hbinary
    exact ⟨transfer B,B,hB,1,one_ne_zero,by simp⟩
  have htor : ∀ B, ActualNonsingular L.family B → ProjectivelyFinite (transfer B) := by
    intro B hB
    apply (hsafe B hB.1 ?_).2
    intro hz
    exact hB.2 (by rw [hz, Matrix.det_zero])
  exact hsafe.diagonal (actualTransfers_projectiveMatrixGroup L.family hne htor)
    (finite_actualClasses P L.family L.family_finite hne htor) D a b hD ha hb

lemma actual_binary_diagonal {F : SignatureFamily AlgebraicComplex}
    (hbinary : ∃ B : AMat, ActualNonsingular F B)
    (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ B : AMat, ActualNonsingular (familyAction D F) B := by
  obtain ⟨B,hB⟩ := hbinary
  have hpull : Kernel.pullback Signature.disequality D.matrix =
      fun x y => (a*b) * Signature.disequality x y := by
    rw [hD]
    exact HeightTwo.diagonalBasis_pullback a b ha hb
  obtain ⟨B',hB',_⟩ := hB.diagonal_transport D a b hD ha hb hpull
  exact ⟨B',hB'⟩

/-- Every strict normalized saturation supplies an actual continuing stage.
The next language is inverse-normalized before re-entering the source's fixed
field, and both encoded reductions are composed through the real languages. -/
theorem RawStage.extend_saturated
    (P : GroupSplit.Paper1Accepted) (PR : Paper1RestrictionAccepted)
    (PN : Paper1NormalizationAccepted) {L : Language} (S : RawStage L)
    (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hconf : XConformal D) (M B : Language)
    (hM : M.family = familyAction D S.language.family)
    (hML : FixedFieldOutput.Reduces .nativeX M S.language)
    (hLM : FixedFieldOutput.Reduces .nativeX S.language M)
    (hB : SourceRetainedExtension M B) (hfac : FactorClosed B.family)
    (hfield : ∀ f ∈ B.family, PullbackOver (originalField L) D f)
    (hsafe : AllBinariesSafe B.family) :
    ∃ T : RawStage L, T.language.family = familyAction D.symm B.family := by
  obtain ⟨A,hA,hfacA,heq,hfieldA,_⟩ := inverse_normalized_retained_stage PR PN
    S.language M B S.retained.preprocessed S.retained.notOneSided D a b hD ha hb hconf
    hM hML hLM hB hfac (originalField L) hfield
  have hbinaryM : ∃ B : AMat, ActualNonsingular M.family B := by
    rw [hM]
    exact actual_binary_diagonal S.binary D a b hD ha hb
  have hbinaryB : ∃ C : AMat, ActualNonsingular B.family C := by
    obtain ⟨C,hC⟩ := hbinaryM
    exact ⟨C,networkRealizable_mono hB.subset hC.1,hC.2⟩
  have hsafeA : AllBinariesSafe A.family := by
    rw [heq]
    exact safe_diagonal P B hsafe hbinaryB D.symm a⁻¹ b⁻¹
      (inverse_diagonal D a b hD ha hb) (inv_ne_zero ha) (inv_ne_zero hb)
  have hbinaryA : ∃ C : AMat, ActualNonsingular A.family C := by
    rw [heq]
    exact actual_binary_diagonal hbinaryB D.symm a⁻¹ b⁻¹
      (inverse_diagonal D a b hD ha hb) (inv_ne_zero ha) (inv_ne_zero hb)
  exact ⟨⟨A,S.retained.trans hA,hfacA,hfieldA,hsafeA,hbinaryA⟩,heq⟩

end
end Paper2.SourceFaithful.HeightOne

