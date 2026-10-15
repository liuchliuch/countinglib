import Paper2.Paper1ProvedOddUnaryIsotropic
import Paper2.Paper1ProvedOddResidueNetwork
import Paper2.SourceFaithful.GadgetAugmentation

/-! An independent pair of actual isotropic original ordinary unaries gives
opposite pure pins on the inverse-K chart. Nonzero fixed graph scalars are
retained in the physical witnesses and removed by the actual controlled gadget
installation. The resulting finite language contains both exact unit pins. -/
namespace Paper2.Paper1Proved.OddUnary.IsotropicPins
open Paper2.Tractable Paper2.ExactInput Paper2.Synthesis
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Ordinary
export GeneralOddUnaryOrdinary (pairing isotropic_diagnostic pairing_diagnostic)
end Ordinary

private theorem purePin_literal (c : AlgebraicComplex) (b : Bool) :
    Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps.purePin c b 1 =
      c • TensorDecomposition.literalPin b := by
  funext x
  have he : x = (fun _ => b) ↔ x 0 = b := by
    constructor
    · intro h; exact congrFun h 0
    · intro h
      funext i
      rw [Fin.eq_zero i,h]
  simp [Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps.purePin,
    TensorDecomposition.literalPin,he,Pi.smul_apply,smul_eq_mul]

/-- The exact scalar forms of an independent isotropic ordinary pair. -/
theorem isotropic_pair_forms (f g : Signature AlgebraicComplex 1)
    (hf : Ordinary.pairing f f = 0) (hg : Ordinary.pairing g g = 0)
    (hcross : Ordinary.pairing f g ≠ 0) :
    ∃ b : Bool, ∃ c d : AlgebraicComplex, c ≠ 0 ∧ d ≠ 0 ∧
      Holant.Tractable.sourceKBasis.symm.action f = c • TensorDecomposition.literalPin b ∧
      Holant.Tractable.sourceKBasis.symm.action g = d • TensorDecomposition.literalPin (!b) := by
  have hfn : f ≠ 0 := by
    intro h
    apply hcross
    simp [Ordinary.pairing,h,Holant.Signature.connect_equality]
  have hgn : g ≠ 0 := by
    intro h
    apply hcross
    simp [Ordinary.pairing,h,Holant.Signature.connect_equality]
  obtain ⟨b,c,hc,hf⟩ := Ordinary.isotropic_diagnostic f hfn hf
  obtain ⟨a,d,hd,hg⟩ := Ordinary.isotropic_diagnostic g hgn hg
  have hab : a = !b := by
    by_contra h
    have he : a = b := by cases a <;> cases b <;> simp_all
    apply hcross
    rw [Ordinary.pairing_diagnostic,hf,hg,he]
    cases b <;> simp [Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps.purePin,funext_iff]
  refine ⟨!b,c,d,hc,hd,?_,?_⟩
  · rw [hf]
    exact purePin_literal c (!b)
  · rw [hg,hab]
    simp only [Bool.not_not]
    simpa only [Bool.not_not] using purePin_literal d b

/-- Literal ordinary-to-native graph transport preserves the true physical
macro, including its boundary order and its nonzero scalar. -/
theorem native_pin_access (L : Language)
    (U V : GeneralOddHighTerminalAccess.Actual (signatures L) 1)
    (hU : GeneralOddNonisotropicFrame.norm U.graph.denote = 0)
    (hV : GeneralOddNonisotropicFrame.norm V.graph.denote = 0)
    (hcross : Ordinary.pairing U.graph.denote V.graph.denote ≠ 0) :
    ∃ b : Bool,
      NativeNetworkRealizesUpTo (inverseKLanguage L).family (TensorDecomposition.literalPin b) ∧
      NativeNetworkRealizesUpTo (inverseKLanguage L).family (TensorDecomposition.literalPin (!b)) := by
  have hu : Ordinary.pairing U.graph.denote U.graph.denote = 0 := by
    simpa only [Isotropic.norm_eq_pairing] using hU
  have hv : Ordinary.pairing V.graph.denote V.graph.denote = 0 := by
    simpa only [Isotropic.norm_eq_pairing] using hV
  obtain ⟨b,c,d,hc,hd,hf,hg⟩ := isotropic_pair_forms U.graph.denote V.graph.denote hu hv hcross
  refine ⟨b,?_,?_⟩
  · have hreal := OddResidue.fromSource_realizable _ (GeneralOddUnaryOrdinary.toNative U.graph)
      (GeneralOddUnaryOrdinary.toNative_uses L.family U.graph U.uses)
      (GeneralOddUnaryOrdinary.toNative_native U.graph U.ordinary)
    rw [GeneralOddUnaryOrdinary.toNative_denote,hf] at hreal
    obtain ⟨N,hN,hX,he⟩ := hreal.ordered
    refine ⟨N,?_,hX,c,hc,?_⟩
    · rw [inverseKLanguage_family]
      exact hN
    · funext x
      simpa only [Pi.smul_apply,smul_eq_mul] using congrFun he x
  · have hreal := OddResidue.fromSource_realizable _ (GeneralOddUnaryOrdinary.toNative V.graph)
      (GeneralOddUnaryOrdinary.toNative_uses L.family V.graph V.uses)
      (GeneralOddUnaryOrdinary.toNative_native V.graph V.ordinary)
    rw [GeneralOddUnaryOrdinary.toNative_denote,hg] at hreal
    obtain ⟨N,hN,hX,he⟩ := hreal.ordered
    refine ⟨N,?_,hX,d,hd,?_⟩
    · rw [inverseKLanguage_family]
      exact hN
    · funext x
      simpa only [Pi.smul_apply,smul_eq_mul] using congrFun he x

/-- Both true unit pins are installed simultaneously in the exact inverse-K
language, with genuine controlled reductions in both directions. -/
theorem isotropic_pair_pins
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (L : Language) (hp : Preprocessed L.family)
    (U V : GeneralOddHighTerminalAccess.Actual (signatures L) 1)
    (hU : GeneralOddNonisotropicFrame.norm U.graph.denote = 0)
    (hV : GeneralOddNonisotropicFrame.norm V.graph.denote = 0)
    (hcross : Ordinary.pairing U.graph.denote V.graph.denote ≠ 0) :
    ∃ N : Language, (inverseKLanguage L).family ⊆ N.family ∧
      (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ N.family ∧
      (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ N.family ∧
      Preprocessed N.family ∧ ¬ CommonOneSided N.family ∧
      FixedFieldOutput.Reduces .nativeX N (inverseKLanguage L) ∧
      FixedFieldOutput.Reduces .nativeX (inverseKLanguage L) N := by
  obtain ⟨b,hb,hnb⟩ := native_pin_access L U V hU hV hcross
  have h0 : NativeNetworkRealizesUpTo (inverseKLanguage L).family (TensorDecomposition.literalPin false) := by
    cases b
    · exact hb
    · exact hnb
  have h1 : NativeNetworkRealizesUpTo (inverseKLanguage L).family (TensorDecomposition.literalPin true) := by
    cases b
    · exact hnb
    · exact hb
  obtain ⟨N,hN,hNL⟩ := G.adjoin_pair (inverseKLanguage L)
    (TensorDecomposition.literalPin false) (TensorDecomposition.literalPin true) h0 h1
  have hsub : (inverseKLanguage L).family ⊆ N.family := by
    rw [hN]
    intro f hf
    exact Or.inr (Or.inr hf)
  have p0 : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ N.family := by
    rw [hN]
    exact Or.inl rfl
  have p1 : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ N.family := by
    rw [hN]
    exact Or.inr (Or.inl rfl)
  have hpL : Preprocessed (inverseKLanguage L).family := by
    rw [inverseKLanguage_family]
    exact Conformal.preprocessed_familyAction _ hp
  have hpN : Preprocessed N.family := by
    rw [hN]
    rintro f (rfl | rfl | hf)
    · exact ⟨by decide,TensorDecomposition.literalPin_ne_zero false⟩
    · exact ⟨by decide,TensorDecomposition.literalPin_ne_zero true⟩
    · exact hpL f hf
  have hsN : ¬ CommonOneSided N.family := by
    rintro (hs | hs)
    · have hh := hs _ p0 (fun _ => false) (by simp)
      simp only [charge,weight_false,Nat.cast_zero,mul_zero,zero_sub] at hh
      norm_num at hh
    · have hh := hs _ p1 (fun _ => true) (by simp)
      simp only [charge,weight_true,Fintype.card_fin] at hh
      norm_num at hh
  exact ⟨N,hsub,p0,p1,hpN,hsN,hNL,R.restriction_2_5 _ _ hsub⟩

end
end Paper2.Paper1Proved.OddUnary.IsotropicPins
