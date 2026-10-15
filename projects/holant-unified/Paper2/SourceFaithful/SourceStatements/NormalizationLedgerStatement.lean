import Paper2.SourceFaithful.SourceStatements.NormalizationLedgerTensor
import Paper2.SourceFaithful.SourceStatements.NormalizationLedgerGroupConvention
import Mathlib.Order.Fin.Basic

/-! Full source Lemma 2.22: coordinate transport along equivalent augmentations.

The initial field is fixed once. A legal sequence supplies precisely the two
operations printed in the source, with actual public encoded augmentation
reductions and arbitrary algebraic GO(X) normalizations. Every invariant,
tensor-over-field representation, group comparison, tractability implication,
and the literal common basis `W = A⁻¹ V` is proved below.

For transfer groups, the neutral native wire is included by subgroup closure.
The safe nonempty convention agrees with the existing all-realizable subgroup
by `transferGroup_safe`; the empty actual-class set gives the trivial group.
This convention does not assume an unavailable vertex-free arity-two network.
-/
namespace Paper2.SourceFaithful.SourceStatements.NormalizationLedger
noncomputable section
open Tractable Tractable.Conformal ExactInput
open Paper2.HeightOne.PhaseCards Paper2.HeightOne.GroupSplit
open Paper2.HeightOne.GroupSplit.MatrixGroup

/-- All conclusions of the printed coordinate-transport lemma. Group descent
and monotonicity are proved at every index, which also covers every consecutive
sequence of the source's safe residual indices. -/
structure Statement (E : Subfield AlgebraicComplex) (G : Language) (n : ℕ)
    (sequence : FiniteSequence E G n) : Prop where
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
  normalizationUnchanged : ∀ i : Fin n, ∀ D : InvertibleKernel, XConformal D →
    (sequence.state i.succ).coordinates = D.comp (sequence.state i.castSucc).coordinates →
    (sequence.state i.succ).language.family =
      familyAction D (sequence.state i.castSucc).language.family →
    pullbackGroup (sequence.state i.succ).coordinates (sequence.state i.succ).language.family =
      pullbackGroup (sequence.state i.castSucc).coordinates
        (sequence.state i.castSucc).language.family
  augmentationEnlarges : ∀ i : Fin n,
    (sequence.state i.succ).coordinates = (sequence.state i.castSucc).coordinates →
    (sequence.state i.castSucc).language.family ⊆ (sequence.state i.succ).language.family →
    pullbackGroup (sequence.state i.castSucc).coordinates
        (sequence.state i.castSucc).language.family ≤
      pullbackGroup (sequence.state i.succ).coordinates (sequence.state i.succ).language.family
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

/-- Literal source 2.22, for every finite permitted sequence and one original
field containing the original coefficients. No diagonal, unary, safe-binary,
actual-binary-existence, tractability, or basis conclusion is assumed. -/
theorem source_2_22 (E : Subfield AlgebraicComplex) (G : Language) (n : ℕ)
    (sequence : FiniteSequence E G n) (initialField : OriginalCoefficients E G) :
    Statement E G n sequence := by
  have hledger := ledger_all_indices E G n sequence initialField.projective
  refine ⟨hledger, fun i => (hledger i).projectiveImage,
    fun i => (hledger i).group_in_original_field,
    fun i => pullbackGroup_eq_conjugate _ _, ?_, ?_, ?_,
    fun i => (hledger i).tract,
    fun i C hC V hV => (hledger i).commonBasis C hC V hV, ?_, ?_, ?_⟩
  · exact Fin.monotone_iff_le_succ.mpr (fun i => (sequence.step i).group_mono)
  · intro i D hD hA hF
    rw [hA, hF]
    exact pullbackGroup_normalize _ D hD _
  · intro i hA hsub
    rw [hA]
    exact pullbackGroup_augment _ hsub
  · intro i V hV
    exact (hledger i).commonBasis affineClass
      (nonzeroScaleClosed_of_scaleClosed affineClass_scaleClosed) V hV
  · intro i V hV
    exact (hledger i).commonBasis productClass
      (nonzeroScaleClosed_of_scaleClosed productClass_scaleClosed) V hV
  · intro i V hV
    exact (hledger i).commonBasis localAffineClass
      (nonzeroScaleClosed_of_scaleClosed localAffineClass_scaleClosed) V hV

end
end Paper2.SourceFaithful.SourceStatements.NormalizationLedger

