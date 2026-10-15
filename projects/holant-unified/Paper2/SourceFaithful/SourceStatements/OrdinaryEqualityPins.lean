import Paper2.SourceFaithful.SourceStatements.OrdinaryEqualityPinsControlled
import Paper2.Paper1ProvedOddUnaryTables
import Paper2.Paper1ProvedOracleAdapters

/-! Literal ordinary arm of source Corollary 3.5. The actual two-copy
equality graph supplies the anchor of the executed two-pin programme.
Every intermediate oracle is length controlled, and the original family
is recovered on the same graph bytes through its inverse-K interpretation.
-/
namespace Paper2.SourceFaithful.SourceStatements.OrdinaryEqualityPins
open Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.Synthesis
open Paper2.Complexity Paper2.Paper1Proved
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.TetrahedralCompletion
open OrdinaryEqualityPinsSource
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def toInverse (L : Language) := FixedFieldOutput.sameValueReduction
  .ordinary .nativeX L (inverseKLanguage L) (inverseKInstanceEquiv L)
  (FixedFieldOutput.sameBytesComputes _ _ _ (inverseKInstance_bytes L))
  (fun G => (inverseKInstance_value L G).symm)

def fromInverse (L : Language) := FixedFieldOutput.sameValueReduction
  .nativeX .ordinary (inverseKLanguage L) L (inverseKInstanceEquiv L).symm
  (FixedFieldOutput.sameBytesComputes _ _ _ (fun G => by
    have h := inverseKInstance_bytes L ((inverseKInstanceEquiv L).symm G)
    simpa only [Equiv.apply_symm_apply] using h.symm))
  (fun G => by
    have h := inverseKInstance_value L ((inverseKInstanceEquiv L).symm G)
    simpa only [Equiv.apply_symm_apply] using h)

/-- Literal subfamily inclusion, with the actual finite label scanner and
both fixed rational answer converters. -/
theorem restriction (L M : Language) (h : L.family ⊆ M.family) :
    FixedFieldOutput.Reduces .ordinary L M := by
  have hi : (inverseKLanguage L).family ⊆ (inverseKLanguage M).family := by
    rw [inverseKLanguage_family,inverseKLanguage_family]
    exact Set.image_mono h
  obtain ⟨r⟩ := Paper1Proved.restriction (inverseKLanguage L) (inverseKLanguage M) hi
  exact ⟨(toInverse L).controlledCompose (r.controlledCompose (fromInverse M))⟩

abbrev palette (L : Language) {d : ℕ} (hd : 4 ≤ d)
    (heq : (⟨d,DegreeCSP.equality (K := AlgebraicComplex) d⟩ :
      AnySignature AlgebraicComplex) ∈ L.family) :=
  OddUnary.Tables.fieldLanguage
    (OrdinaryBothPins.Source.paletteArity (table L) (anchor L hd heq))
    (OrdinaryBothPins.Single.K (table L) (anchor L hd heq))
    (OrdinaryBothPins.Source.palette (table L) (anchor L hd heq))

theorem palette_family (L : Language) {d : ℕ} (hd : 4 ≤ d)
    (heq : (⟨d,DegreeCSP.equality (K := AlgebraicComplex) d⟩ :
      AnySignature AlgebraicComplex) ∈ L.family) :
    (palette L hd heq).family =
      ((L.family ∪ {⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩}) ∪
        {⟨1,TensorDecomposition.literalPin false⟩}) ∪
        {⟨1,TensorDecomposition.literalPin true⟩} := by
  rw [OddUnary.Tables.family]
  exact OrdinaryEqualityPinsSource.palette_family L hd heq

/-- The actual palette programme followed by the exact original-field
decoder and the byte-identical ordinary/native interpretation. -/
theorem palette_reduction (L : Language) {d : ℕ} (hd : 4 ≤ d)
    (heq : (⟨d,DegreeCSP.equality (K := AlgebraicComplex) d⟩ :
      AnySignature AlgebraicComplex) ∈ L.family) :
    FixedFieldOutput.Reduces .ordinary (palette L hd heq) L := by
  let A := anchor L hd heq
  let K := OrdinaryBothPins.Single.K (table L) A
  let F := OrdinaryBothPins.Single.F (table L) A
  let ar := OrdinaryBothPins.Source.paletteArity (table L) A
  let H := OrdinaryBothPins.Source.palette (table L) A
  let embed : K →ₗ[ℚ] AlgebraicComplex := K.val.toLinearMap
  let r := OrdinaryEqualityPinsControlled.programme L hd heq
  let first := sourceFieldAdapter .ordinary (palette L hd heq)
    (OrdinaryBothPins.Source.inputEncoding (table L) A) F embed
    (OrdinaryBothPins.Source.value (table L) A) (OddUnary.Tables.fieldInput ar K H)
    (OddUnary.Tables.inputComputes ar (OddUnary.Tables.mapped ar K H))
    r.sourceOutputBound (OddUnary.Tables.field_value_correct ar K F H)
  let last := fieldTargetReduction .nativeX (inverseKLanguage L)
    (originalPresentation (inverseKLanguage L)) (originalEmbedding (inverseKLanguage L))
    Subtype.val_injective (originalValue (inverseKLanguage L))
    (originalEmbedding_correct (inverseKLanguage L))
  exact ⟨first.controlledCompose (r.controlledCompose (last.controlledCompose (fromInverse L)))⟩

/-- Finite Turing-equivalent pin enlargement of the original ordinary
language. No preprocessing, direct pin graph or extra identity resource is
assumed; the ordinary identity edges are part of this problem's definition.+-/
theorem corollary_3_5_ordinary (L : Language) {d : ℕ} (hd : 4 ≤ d)
    (heq : (⟨d,DegreeCSP.equality (K := AlgebraicComplex) d⟩ :
      AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ M : Language,
      M.family = L.family ∪ Set.range (fun b : Bool =>
        (⟨1,TensorDecomposition.literalPin b⟩ : AnySignature AlgebraicComplex)) ∧
      FixedFieldOutput.Reduces .ordinary M L ∧ FixedFieldOutput.Reduces .ordinary L M := by
  obtain ⟨M,hM⟩ := Language.coverage_family
    (L.family ∪ Set.range (fun b : Bool =>
      (⟨1,TensorDecomposition.literalPin b⟩ : AnySignature AlgebraicComplex)))
    (L.family_finite.union (Set.finite_range _))
  have hMP : M.family ⊆ (palette L hd heq).family := by
    rw [hM,palette_family]
    rintro f (hf | ⟨b,rfl⟩)
    · exact Or.inl (Or.inl (Or.inl hf))
    · cases b
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr rfl
  have hLM : L.family ⊆ M.family := by rw [hM]; exact Set.subset_union_left
  exact ⟨M,hM,(restriction M _ hMP).trans (palette_reduction L hd heq),restriction L M hLM⟩

end
end Paper2.SourceFaithful.SourceStatements.OrdinaryEqualityPins

