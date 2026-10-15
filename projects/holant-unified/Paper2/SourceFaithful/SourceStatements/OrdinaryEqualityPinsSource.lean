import Paper2.SourceFaithful.SourceStatements.OrdinaryEqualityGraph
import Paper2.Paper1ProvedCriteria
import Holant.Proofs.Tetrahedral.OrdinaryBothPins.Source
import Holant.NetworkAsGadget

/-! The actual frozen ordinary pin programme specialized to a supplied higher
equality.  The whole original family is inverse-K transported and the same K
is used in the actual anchor and in the programme.  This source interface is
the frozen `PolyTimeOracleReduction`; it does not assert the stronger separate
length-controlled adapter merely from that type. -/
namespace Paper2.SourceFaithful.SourceStatements.OrdinaryEqualityPinsSource
open Paper2.Tractable Paper2.ExactInput Paper2.Paper1Proved Paper2.Synthesis
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev table (L : Language) := signatures (inverseKLanguage L)
abbrev basis := invertibleKernelIso sourceKBasis

theorem anchor_exists (L : Language) {d : ℕ} (hd : 4 ≤ d)
    (heq : (⟨d,DegreeCSP.equality (K := AlgebraicComplex) d⟩ :
      AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ A : QuaternaryEqualityTerminal.AnchorStep (Holant.Complexity.UniversalPairReduction.FiniteFamily.family (table L)),
      A.basis = basis := by
  obtain ⟨G,hU,hI,hG⟩ := OrdinaryEqualityGraph.equality_four_realized L (by omega) heq
  have hg := OddUnary.ordinary_network_inverseK L G hU hI
  rw [hG] at hg
  obtain ⟨N,hN,hX,hn⟩ := hg.ordered
  have actual : Holant.Gadget.Realizes (Holant.Complexity.UniversalPairReduction.FiniteFamily.family (table L))
      .disequality OddUnary.nativeEqualityFour := by
    change Holant.Gadget.Realizes _ .disequality
      (sourceKBasis.symm.action Holant.EightVertex.ProductAnchor.equalityFour)
    rw [← hn]
    exact Holant.Gadget.realizes_network (sourceNetwork N) _ .disequality hN hX
  refine ⟨{
    signature := OddUnary.nativeEqualityFour
    basis := basis
    edgeScale := 1
    vertexScale := 1
    edge_ne_zero := one_ne_zero
    vertex_ne_zero := one_ne_zero
    actual := actual
    edge_exact := ?_
    anchor_exact := ?_ },rfl⟩
  · change Kernel.pullback Signature.disequality KInverse = _
    rw [Paper2.ExactInput.Computation.inverseK_pullback]
    funext a b
    simp [Paper2.Signature.equality,Holant.Signature.equality]
  · change sourceKBasis.action (sourceKBasis.symm.action
      Holant.EightVertex.ProductAnchor.equalityFour) = _
    simpa only [one_mul] using InvertibleKernel.action_symm_action sourceKBasis
      (Holant.EightVertex.ProductAnchor.equalityFour : Signature AlgebraicComplex 4)

def anchor (L : Language) {d : ℕ} (hd : 4 ≤ d)
    (heq : (⟨d,DegreeCSP.equality (K := AlgebraicComplex) d⟩ :
      AnySignature AlgebraicComplex) ∈ L.family) :
    QuaternaryEqualityTerminal.AnchorStep (Holant.Complexity.UniversalPairReduction.FiniteFamily.family (table L)) :=
  Classical.choose (anchor_exists L hd heq)

theorem anchor_basis (L : Language) {d : ℕ} (hd : 4 ≤ d)
    (heq : (⟨d,DegreeCSP.equality (K := AlgebraicComplex) d⟩ :
      AnySignature AlgebraicComplex) ∈ L.family) :
    (anchor L hd heq).basis = basis := Classical.choose_spec (anchor_exists L hd heq)

/-- This is the real existing finite oracle programme, with its original
number-field answer encoding and physical ordinary palette. -/
def programme (L : Language) {d : ℕ} (hd : 4 ≤ d)
    (heq : (⟨d,DegreeCSP.equality (K := AlgebraicComplex) d⟩ :
      AnySignature AlgebraicComplex) ∈ L.family) :=
  Source.top (table L) (anchor L hd heq)

/-- The same algebraic K cancels on every original row.  The added equality
four is supplied by the actual two-copy graph, and both unit pins are the
literal ordinary rows of the executed source programme. -/
theorem palette_family (L : Language) {d : ℕ} (hd : 4 ≤ d)
    (heq : (⟨d,DegreeCSP.equality (K := AlgebraicComplex) d⟩ :
      AnySignature AlgebraicComplex) ∈ L.family) :
    Set.range (fun i => RingHomRealization.mapAny
      (Single.K (table L) (anchor L hd heq)).subtype
      (⟨Source.paletteArity (table L) (anchor L hd heq) i.val,
        Source.palette (table L) (anchor L hd heq) i⟩ :
        Holant.AnySignature (Single.K (table L) (anchor L hd heq)))) =
      ((L.family ∪ {⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩}) ∪
        {⟨1,fun x => if x 0 = false then (1 : AlgebraicComplex) else 0⟩}) ∪
        {⟨1,fun x => if x 0 = true then (1 : AlgebraicComplex) else 0⟩} := by
  rw [Source.palette_ambient,anchor_basis]
  have hf : Holant.Tractable.familyAction basis
      (Holant.Complexity.UniversalPairReduction.FiniteFamily.family (table L)) = L.family := by
    change kImage (inverseKLanguage L) = L.family
    exact kImage_inverseKLanguage L
  rw [hf]
  rfl

/-- The target raw record and value are precisely the original ordinary
problem, after the literal inverse-K interpretation of the same bytes. -/
theorem target_value (L : Language)
    (r : Holant.Complexity.ExactSignatureTables.Input
      (inverseKLanguage L).count 1 (inverseKLanguage L).arity) :
    ((Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget.originalValue
      (table L) r : Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget.originalField
      (table L)) : AlgebraicComplex) =
      Problem.value .ordinary L
        ((inverseKInstanceEquiv L).symm ((inputIso (inverseKLanguage L)).symm r)) := by
  rw [Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget.target_exact]
  change Problem.value .nativeX (inverseKLanguage L) ((inputIso (inverseKLanguage L)).symm r) = _
  have hv := inverseKInstance_value L
    ((inverseKInstanceEquiv L).symm ((inputIso (inverseKLanguage L)).symm r))
  simpa only [Equiv.apply_symm_apply] using hv

end
end Paper2.SourceFaithful.SourceStatements.OrdinaryEqualityPinsSource

