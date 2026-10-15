import Paper2.Paper1ProvedGraph
import Paper2.Paper1ProvedCriteria
import Paper2.Paper1Accepted
import Holant.Tractable.Anchor
import Holant.Proofs.Dichotomy.Main.PaperMainTheorems
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryPositive

/-! Concrete instances of the proved Paper 1 classification results on the
literal Paper 2 family. The finite Boolean programmes and length-controlled
hardness are retained before transporting their chosen-field answer encoding.
This file introduces no accepted-result parameter. -/
namespace Paper2.Paper1Proved
open Paper2.Tractable Paper2.ExactInput Paper2.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
noncomputable section
set_option backward.isDefEq.respectTransparency false

@[simp] theorem kImage (L : Language) :
    Paper2.kImage L = Holant.Tractable.familyAction Holant.Tractable.sourceKBasis L.family := rfl

/-- The binary equality row becomes the literal binary Z anchor. -/
theorem equalityAnchor (L : Language) (h : HasLiteralEquality L) :
    Tract (Paper2.kImage L) ↔ TractX (Paper2.kImage L) := by
  have hz : Holant.Tractable.sourceKBasis.action
      (Holant.Tractable.kernelSignature Holant.Signature.equality) =
      Holant.Tractable.zAnchor := by
    have he := Holant.Tractable.InvertibleKernel.action_symm_action
      Holant.Tractable.sourceKBasis Holant.Tractable.zAnchor
    rw [Holant.Tractable.sourceKBasis_symm_action_zAnchor] at he
    exact he
  have member : (⟨2,Holant.Tractable.zAnchor⟩ :
      Holant.AnySignature AlgebraicComplex) ∈ Paper2.kImage L := by
    exact ⟨⟨2,Holant.Tractable.kernelSignature Holant.Signature.equality⟩,h,
      congrArg (Sigma.mk 2) hz⟩
  exact (tract_iff _).trans
    ((Holant.Tractable.tract_iff_tractX_of_zAnchor_mem member).trans (tractX_iff _).symm)

abbrev nativePresentation (L : Language) :=
  OriginalFamily.presentation (signatures L) (kernels .nativeX)

abbrev nativeValue (L : Language) :=
  OriginalFamily.value (signatures L) (kernels .nativeX)

/-- The actual four-branch evaluator of the unchanged native-X input. -/
def nativeComputesOfTractX (L : Language) (h : TractX (Paper2.kImage L)) :
    Holant.Complexity.BinaryCompose.Computes
      (Holant.Complexity.RawClosedNetwork.validatedEncoding L.count 1 L.arity)
      (nativePresentation L).encoding (nativeValue L) :=
  TractXCoreSource.nativeComputesOfKTractX (signatures L) L.family
    (fun i => ⟨i,rfl⟩) L.family_finite ((tractX_iff _).mp h)

/-- The source implementation retains the complete query and answer bounds. -/
theorem literalEqualityControlledHard (L : Language) (h : HasLiteralEquality L)
    (hn : ¬ TractX (Paper2.kImage L)) :
    (PaperLiteralEqualityHardness.target (signatures L)).Hard := by
  obtain ⟨j,hj⟩ := h
  exact PaperLiteralEquality.controlledNegative (signatures L) j hj
    (fun ht => hn ((tractX_iff _).mpr ht))

private theorem endpointEven (q : Signature AlgebraicComplex 4)
    (he : ∀ x, Odd (Paper2.weight x) → q x = 0)
    (hn : q (fun _ => false) * q (fun _ => true) ≠ 0) :
    Holant.EightVertex.ProductAnchor.EndpointEven q := by
  refine ⟨(mul_ne_zero_iff.mp hn).1,(mul_ne_zero_iff.mp hn).2,?_⟩
  intro x hx
  exact he x (Nat.odd_iff.mpr hx)

/-- A full Boolean-stack evaluator from the actual endpoint theorem. The
proved Paper 1 implementation establishes the stronger endpoint conclusion;
the supplied Paper 2 tensor-prime hypothesis is therefore sufficient. -/
def quaternaryComputes (L : Language) (h : HasPrimeEightVertex L)
    (ht : Tract (Paper2.kImage L)) :
    Holant.Complexity.BinaryCompose.Computes
      (Holant.Complexity.RawClosedNetwork.validatedEncoding L.count 1 L.arity)
      (nativePresentation L).encoding (nativeValue L) := by
  let q := Classical.choose h
  have hq := Classical.choose_spec h
  have member := hq.1
  have even := hq.2.2.1
  have endpoint := hq.2.2.2
  exact PaperQuaternaryPositive.computesOfTract (signatures L) member
    (endpointEven q even endpoint) ((tract_iff _).mp ht)

theorem quaternaryControlledHard (L : Language) (h : HasPrimeEightVertex L)
    (hn : ¬ Tract (Paper2.kImage L)) :
    (PaperLiteralEqualityHardness.target (signatures L)).Hard := by
  obtain ⟨q,⟨j,literal⟩,_prime,even,endpoint⟩ := h
  exact PaperQuaternary.controlledNegative (signatures L) q j literal
    (endpointEven q even endpoint) (fun ht => hn ((tract_iff _).mpr ht))

end
end Paper2.Paper1Proved
