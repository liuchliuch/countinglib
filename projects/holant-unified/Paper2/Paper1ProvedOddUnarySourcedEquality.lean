import Paper2.Paper1ProvedOddUnaryTables
import Paper2.Paper1ProvedOddUnaryPaired
import Holant.Proofs.Hardness.GeneralOddHighTerminalAccess

/-! A physical paired-unary receipt is consumed at the unchanged original
ordinary oracle. The strict field-table programme and both rational answer
converters remain part of the actual canonical reduction. -/
namespace Paper2.Paper1Proved.OddUnary
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Holant.Algebraic
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem original_ordinary_field_correct (L : Language) (G : SourceInput L) :
    (GeneralOddHighTerminalAccess.targetValue (signatures L) G : AlgebraicComplex) =
      Paper2.Problem.value .ordinary L ((inputIso L).symm G) := by
  rw [Holant.LocalDrafts.MainChain.OriginalFamily.value_exact]
  have h := network_value .ordinary L ((inputIso L).symm G)
  change (((inputIso L) ((inputIso L).symm G)).val.realize
    (((inputIso L) ((inputIso L).symm G)).property) (signatures L) (kernels .ordinary)).denote
      Fin.elim0 = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h

variable {s degree : ℕ} {a : ℕ → ℕ}
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
local instance : CharZero K := Algebra.charZero_of_charZero ℚ K
variable (F : FixedField K degree) (H : (i : Fin s) → Holant.Signature K (a i.val))
variable (L : Language)
variable (back : Holant.Complexity.LengthControlledOracleReduction
  (Holant.Complexity.RawClosedNetwork.validatedEncoding s 1 a) F.encoding
  (sourceEncoding L) (GeneralOddHighTerminalAccess.presentation (signatures L)).encoding
  ((QuaternaryOrdinaryCompanion.tables F H).evaluate F)
  (GeneralOddHighTerminalAccess.targetValue (signatures L)))

include F back in
/-- The source field table is represented literally, with the same graph
bytes. No response selection, free graph resource or idealized field operation
is inserted into the controlled programme. -/
theorem table_reduction : FixedFieldOutput.Reduces .ordinary (Tables.fieldLanguage a K H) L := by
  let E := GeneralOddHighTerminalAccess.presentation (signatures L)
  let embed : K →ₗ[ℚ] AlgebraicComplex := K.val.toLinearMap
  let targetEmbed : GeneralOddHighTerminalAccess.field (signatures L) →ₗ[ℚ] AlgebraicComplex :=
    (GeneralOddHighTerminalAccess.field (signatures L)).val.toLinearMap
  exact ⟨canonicalReduction .ordinary .ordinary (Tables.fieldLanguage a K H) L
    (Holant.Complexity.RawClosedNetwork.validatedEncoding s 1 a) F embed
    (Tables.fieldValue a K F H) (Tables.fieldInput a K H)
    (Tables.inputComputes a (Tables.mapped a K H)) (Tables.field_value_correct a K F H)
    E targetEmbed Subtype.val_injective
    (GeneralOddHighTerminalAccess.targetValue (signatures L)) (original_ordinary_field_correct L) back⟩

include F back in
/-- The actual scalar Eq4 graph of a sourced finite table is sufficient at
the original ordinary target, without invoking the odd-language classification. -/
theorem sourced_equality_hard
    (P : SourceFaithful.Paper1Accepted) (PG : SourceFaithful.Paper1DirectGadgetAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted) (PF : SourceFaithful.Paper1FactorClosureAccepted)
    (PN : SourceFaithful.Paper1NormalizationAccepted)
    (negative : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H))
    (G : OrdinaryNegativeCubicGadgets.Macro H 4) (c : K) (hc : c ≠ 0)
    (hG : G.network.denote = c • Holant.EightVertex.ProductAnchor.equalityFour) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  have hn : ¬ Tract (Tables.fieldLanguage a K H).family := by
    intro ht
    apply negative
    rw [Tables.family] at ht
    exact (tract_iff _).mp ht
  have hu : ∀ v, (⟨(G.network.map K.subtype).shape.arity v,
      (G.network.map K.subtype).vertex v⟩ : AnySignature AlgebraicComplex) ∈
        (Tables.fieldLanguage a K H).family := by
    intro v
    rw [Tables.family]
    refine ⟨G.labels.vertex v,?_⟩
    exact congrArg (RingHomRealization.mapAny K.subtype) (G.exact v)
  have he : ∀ e, (G.network.map K.subtype).edge e = Holant.Signature.equality := by
    intro e
    funext u v
    change K.subtype (G.network.edge e u v) = _
    rw [G.edges]
    cases u <;> cases v <;> simp [Holant.Signature.equality]
  have hc' : (c : AlgebraicComplex) ≠ 0 := fun hz => hc (Subtype.ext hz)
  have hv : (G.network.map K.subtype).denote =
      fun x => (c : AlgebraicComplex) * Holant.EightVertex.ProductAnchor.equalityFour x := by
    funext x
    rw [Holant.Network.denote_map,hG]
    simp only [Pi.smul_apply,smul_eq_mul,map_mul]
    congr 1
    simp [Holant.EightVertex.ProductAnchor.equalityFour,apply_ite]
  exact (ordinary_equalityFour_hard P PG PR PF PN (Tables.fieldLanguage a K H) hn
    (G.network.map K.subtype) hu he c hc' hv).transport (table_reduction K F H L back)

include back in
/-- The genuine paired-series receipt contains its own scalar equality graph,
old-row inclusion and interpolation programme. All three are consumed here. -/
theorem receipt_hard
    (P : SourceFaithful.Paper1Accepted) (PG : SourceFaithful.Paper1DirectGadgetAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted) (PF : SourceFaithful.Paper1FactorClosureAccepted)
    (PN : SourceFaithful.Paper1NormalizationAccepted)
    (negative : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H))
    (D : GlobalCloseCompletionPairedSeriesReceipt.Receipt H F) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  have hi : GlobalCloseCompletionUnaryDescentSource.ambient K H ⊆
      GlobalCloseCompletionUnaryDescentSource.ambient K D.table := by
    rintro f ⟨i,rfl⟩
    exact ⟨D.old i,congrArg (RingHomRealization.mapAny K.subtype) (D.old_literal i)⟩
  have hn : ¬ Holant.Tractable.Tract (GlobalCloseCompletionUnaryDescentSource.ambient K D.table) :=
    fun ht => negative (ht.mono_family hi)
  exact sourced_equality_hard K F D.table L (Programme.compose D.source back) P PG PR PF PN hn
    D.graph D.scalar D.nonzero D.value

end
end Paper2.Paper1Proved.OddUnary

