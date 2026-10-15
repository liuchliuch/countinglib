import Paper2.SourceFaithful.SourceStatements.NormalizationLedgerBasis
import Paper2.SourceFaithful.SourceStatements.PublicReduction
import Paper2.Paper1ProvedNormalizationProvider
import Paper2.Paper1ProvedRestrictionProvider
import Paper2.HeightOne.PhaseCards.DiagonalFieldSaturation

/-! Finite sequences of the two literal source normalization-ledger steps.
Augmentations carry the permitted actual encoded reduction and the original
fixed-field condition on new tensors. Normalizations carry an arbitrary
invertible GO(X) matrix. All conclusions below are derived by finite induction. -/
namespace Paper2.SourceFaithful.SourceStatements.NormalizationLedger
noncomputable section
open Tractable Tractable.Conformal ExactInput
open Paper2.HeightOne.PhaseCards

structure State where
  coordinates : InvertibleKernel
  language : Language
  preprocessed : Preprocessed language.family

/-- These are exactly the two allowed operations, rather than assumed ledger
conclusions. The normalization multiplier is recorded in `XConformal`. -/
inductive LegalStep (E : Subfield AlgebraicComplex) : State → State → Prop
  | augment {S T : State}
      (sameCoordinates : T.coordinates = S.coordinates)
      (retained : S.language.family ⊆ T.language.family)
      (backward : Problem.Reduces .nativeX T.language S.language)
      (newField : ∀ f ∈ T.language.family, f ∉ S.language.family →
        PullbackOver E S.coordinates f) : LegalStep E S T
  | normalize {S T : State} (D : InvertibleKernel)
      (conformal : XConformal D)
      (coordinates : T.coordinates = D.comp S.coordinates)
      (family : T.language.family = familyAction D S.language.family) : LegalStep E S T

structure FiniteSequence (E : Subfield AlgebraicComplex) (G : Language) (n : ℕ) where
  state : Fin (n + 1) → State
  initialCoordinates : (state 0).coordinates = InvertibleKernel.identity
  initialFamily : (state 0).language.family = G.family
  step : ∀ i : Fin n, LegalStep E (state i.castSucc) (state i.succ)

/-- Fixed original-coordinate information at one index. Both reductions are
strict public selector reductions through the actual compiled output codecs. -/
structure Ledger (E : Subfield AlgebraicComplex) (G : Language) (S : State) : Prop where
  retained : familyAction S.coordinates G.family ⊆ S.language.family
  conformal : XConformal S.coordinates
  forward : Problem.Reduces .nativeX G S.language
  backward : Problem.Reduces .nativeX S.language G
  field : ∀ f ∈ S.language.family, PullbackOver E S.coordinates f

lemma public_restriction (L M : Language) (h : L.family ⊆ M.family) :
    Problem.Reduces .nativeX L M :=
  PublicReduction.of_fixed_field .nativeX L M (Paper1Proved.restriction L M h)

lemma Ledger.advance {E : Subfield AlgebraicComplex} {G : Language} {S T : State}
    (h : Ledger E G S) (step : LegalStep E S T) : Ledger E G T := by
  classical
  cases step with
  | augment hA hsub hback hnew =>
    refine ⟨?_, ?_, h.forward.trans (public_restriction _ _ hsub),
      hback.trans h.backward, ?_⟩
    · rw [hA]
      exact h.retained.trans hsub
    · rw [hA]
      exact h.conformal
    · intro f hf
      rw [hA]
      by_cases hold : f ∈ S.language.family
      · exact h.field f hold
      · exact hnew f hf hold
  | normalize D hD hA hfamily =>
    obtain ⟨hback, hforward⟩ :=
      Paper1Proved.normalizationProvider.normalization_2_26
        S.language S.preprocessed D hD T.language hfamily
    refine ⟨?_, ?_,
      h.forward.trans (PublicReduction.of_fixed_field .nativeX _ _ hforward),
      (PublicReduction.of_fixed_field .nativeX _ _ hback).trans h.backward, ?_⟩
    · rw [hA, familyAction_comp, hfamily]
      exact familyAction_mono D h.retained
    · rw [hA]
      exact conformal_comp hD h.conformal
    · intro f hf
      rw [hfamily] at hf
      obtain ⟨g, hg, rfl⟩ := hf
      rw [hA]
      exact (pullbackOver_global E S.coordinates D g).mpr (h.field g hg)

/-- Every index in any actual finite legal sequence has the source ledger
invariants. No number of operations or diagonal restriction is imposed. -/
theorem ledger_all_indices (E : Subfield AlgebraicComplex) (G : Language) (n : ℕ)
    (sequence : FiniteSequence E G n)
    (initialField : ∀ f ∈ G.family, ProjectivelyOver E f.2) :
    ∀ i, Ledger E G (sequence.state i) := by
  apply Fin.induction
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [sequence.initialCoordinates, sequence.initialFamily, familyAction_identity]
    · rw [sequence.initialCoordinates]
      exact conformal_identity
    · apply public_restriction
      rw [sequence.initialFamily]
    · apply public_restriction
      rw [sequence.initialFamily]
    · rw [sequence.initialFamily, sequence.initialCoordinates]
      intro f hf
      simpa only [PullbackOver, InvertibleKernel.identity_symm,
        InvertibleKernel.identity_action] using initialField f hf
  · intro i ih
    exact ih.advance (sequence.step i)

lemma Ledger.tract {E : Subfield AlgebraicComplex} {G : Language} {S : State}
    (h : Ledger E G S) (htract : Tract (familyAction sourceKBasis S.language.family)) :
    Tract (familyAction sourceKBasis G.family) :=
  tract_pullback S.coordinates h.conformal h.retained htract

lemma Ledger.commonBasis {E : Subfield AlgebraicComplex} {G : Language} {S : State}
    (h : Ledger E G S) (C : SignatureFamily AlgebraicComplex)
    (hC : NonzeroScaleClosed C) (V : InvertibleKernel)
    (hV : IsCommonKBasis C S.language.family V) :
    IsCommonKBasis C G.family (S.coordinates.symm.comp V) :=
  commonKBasis_pullback hC S.coordinates V h.conformal h.retained hV

end
end Paper2.SourceFaithful.SourceStatements.NormalizationLedger

