import Paper2.SourceFaithful.SourceStatements.NormalizationLedgerStatement

/-! The source's unrestricted sequence quantifier. No termination premise is
needed: each original index is covered by its actual finite prefix. This is
the form available before the later finite-group termination argument. -/
namespace Paper2.SourceFaithful.SourceStatements.NormalizationLedger
noncomputable section
open Tractable ExactInput Paper2.HeightOne.PhaseCards
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup

structure NaturalSequence (E : Subfield AlgebraicComplex) (G : Language) where
  state : ℕ → State
  initialCoordinates : (state 0).coordinates = InvertibleKernel.identity
  initialFamily : (state 0).language.family = G.family
  step : ∀ i, LegalStep E (state i) (state (i + 1))

def NaturalSequence.prefix {E : Subfield AlgebraicComplex} {G : Language}
    (sequence : NaturalSequence E G) (n : ℕ) : FiniteSequence E G n where
  state := fun i => sequence.state i.val
  initialCoordinates := sequence.initialCoordinates
  initialFamily := sequence.initialFamily
  step := fun i => sequence.step i.val

structure NaturalStatement (E : Subfield AlgebraicComplex) (G : Language)
    (sequence : NaturalSequence E G) : Prop where
  finitePrefixes : ∀ n, Statement E G n (sequence.prefix n)
  invariants : ∀ i, Ledger E G (sequence.state i)
  tensorField : ∀ i, ∀ f ∈ (sequence.state i).language.family,
    ProjectiveImageOver E (sequence.state i).coordinates f
  fixedGroupField : ∀ i,
    pullbackGroup (sequence.state i).coordinates (sequence.state i).language.family ≤
      (pglMap E.subtype).range
  groupFormula : ∀ i,
    pullbackGroup (sequence.state i).coordinates (sequence.state i).language.family =
      (transferGroup (sequence.state i).language.family).map
        (MulAut.conj ((basisClass (sequence.state i).coordinates)⁻¹)).toMonoidHom
  groupMonotone : Monotone (fun i =>
    pullbackGroup (sequence.state i).coordinates (sequence.state i).language.family)
  normalizationUnchanged : ∀ i, ∀ D : InvertibleKernel, XConformal D →
    (sequence.state (i + 1)).coordinates = D.comp (sequence.state i).coordinates →
    (sequence.state (i + 1)).language.family = familyAction D (sequence.state i).language.family →
    pullbackGroup (sequence.state (i + 1)).coordinates (sequence.state (i + 1)).language.family =
      pullbackGroup (sequence.state i).coordinates (sequence.state i).language.family
  augmentationEnlarges : ∀ i,
    (sequence.state (i + 1)).coordinates = (sequence.state i).coordinates →
    (sequence.state i).language.family ⊆ (sequence.state (i + 1)).language.family →
    pullbackGroup (sequence.state i).coordinates (sequence.state i).language.family ≤
      pullbackGroup (sequence.state (i + 1)).coordinates (sequence.state (i + 1)).language.family
  tractOriginal : ∀ i,
    Tract (familyAction sourceKBasis (sequence.state i).language.family) →
      Tract (familyAction sourceKBasis G.family)
  commonBasisOriginal : ∀ i, ∀ C : SignatureFamily AlgebraicComplex,
    NonzeroScaleClosed C → ∀ V : InvertibleKernel,
    IsCommonKBasis C (sequence.state i).language.family V →
      IsCommonKBasis C G.family ((sequence.state i).coordinates.symm.comp V)
  affineBasisOriginal : ∀ i, ∀ V : InvertibleKernel,
    IsCommonKBasis affineClass (sequence.state i).language.family V →
      IsCommonKBasis affineClass G.family ((sequence.state i).coordinates.symm.comp V)
  productBasisOriginal : ∀ i, ∀ V : InvertibleKernel,
    IsCommonKBasis productClass (sequence.state i).language.family V →
      IsCommonKBasis productClass G.family ((sequence.state i).coordinates.symm.comp V)
  localAffineBasisOriginal : ∀ i, ∀ V : InvertibleKernel,
    IsCommonKBasis localAffineClass (sequence.state i).language.family V →
      IsCommonKBasis localAffineClass G.family ((sequence.state i).coordinates.symm.comp V)

/-- Full source 2.22 at all indices of any potentially infinite legal
sequence. There is no promise that the construction terminates. -/
theorem source_2_22_natural (E : Subfield AlgebraicComplex) (G : Language)
    (sequence : NaturalSequence E G) (initialField : OriginalCoefficients E G) :
    NaturalStatement E G sequence := by
  have hprefix : ∀ n, Statement E G n (sequence.prefix n) :=
    fun n => source_2_22 E G n (sequence.prefix n) initialField
  have hledger : ∀ i, Ledger E G (sequence.state i) := by
    intro i
    exact (hprefix i).invariants ⟨i, Nat.lt_succ_self i⟩
  refine ⟨hprefix, hledger, fun i => (hledger i).projectiveImage,
    fun i => (hledger i).group_in_original_field,
    fun i => pullbackGroup_eq_conjugate _ _, ?_, ?_, ?_,
    fun i => (hledger i).tract,
    fun i C hC V hV => (hledger i).commonBasis C hC V hV, ?_, ?_, ?_⟩
  · exact monotone_nat_of_le_succ (fun i => (sequence.step i).group_mono)
  · intro i D hD hA hF
    rw [hA, hF]
    exact pullbackGroup_normalize _ D hD _
  · intro i hA hsub
    rw [hA]
    exact pullbackGroup_augment _ hsub
  · intro i V hV
    exact (hprefix i).affineBasisOriginal ⟨i, Nat.lt_succ_self i⟩ V hV
  · intro i V hV
    exact (hprefix i).productBasisOriginal ⟨i, Nat.lt_succ_self i⟩ V hV
  · intro i V hV
    exact (hprefix i).localAffineBasisOriginal ⟨i, Nat.lt_succ_self i⟩ V hV

end
end Paper2.SourceFaithful.SourceStatements.NormalizationLedger

