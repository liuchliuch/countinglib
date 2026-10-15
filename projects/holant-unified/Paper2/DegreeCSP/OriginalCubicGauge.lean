import Paper2.DegreeCSP.OriginalCubicCommonPhase
import Paper2.DegreeCSP.CyclicExponentTransport
import Paper2.DegreeCSP.SignedBundleGauge
import Paper2.DegreeCSP.OriginalFourthPowerGauge

/-! The character chosen from actual original contexts is transported to
their signed coordinate weights. Its fourth root makes every live affine
three-bit original face have cubic ratio one. -/
namespace Paper2.DegreeCSP.OriginalCubicGauge
open Tractable TensorDecomposition
open Holant.Tractable.AffinePhase (Word)
open Holant.Tractable.TwoTranslate (IsAffineMap)
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem signed_weight {n : ℕ} (x : Word n) :
    SignedBundleGauge.weight x=(Paper2.weight x : ℤ) := by
  simp [SignedBundleGauge.weight,SignedBundleGauge.bit,Paper2.weight]

theorem table_twist {n : ℕ} (p : Word 3→Word n) (hp : IsAffineMap p)
    (f : Signature AlgebraicComplex n) (psi : AlgebraicComplex) :
    PartialTernaryCubicContext.table p (OriginalFourthPowerGauge.twist psi f)=
      SignedBundleGauge.wordTwist (PartialTernaryCubicContext.table p f) psi
        (AffineThreeFaceDecoder.decoder p) := by
  funext a b c
  unfold PartialTernaryCubicContext.table OriginalFourthPowerGauge.twist
    SignedBundleGauge.wordTwist
  rw [AffineThreeFaceDecoder.decoder_correct p hp,signed_weight,
    zpow_neg,zpow_natCast,inv_pow]

theorem charge_signed {n k : ℕ} (hk : 0<k)
    (p : Word 3→Word n) (f : Signature AlgebraicComplex n) :
    (PartialTernaryCubicContext.charge p f k : ZMod k)=
      (SignedBundleGauge.signedCharge (AffineThreeFaceDecoder.decoder p) 6 : ZMod k) := by
  have h := OriginalThreeFaceCharges.boundaryCharge_eq_sum hk p 6
  rw [OriginalThreeFaceCharges.boundaryCharge_degree p f k 6] at h
  simpa only [PartialTernaryCubicContext.charge,SignedBundleGauge.signedCharge,
    Int.cast_sum] using h

theorem cubeRatio_twist_eq_one {n k : ℕ} (hk : 0<k)
    (p : Word 3→Word n) (hp : IsAffineMap p)
    (f : Signature AlgebraicComplex n) (theta psi : AlgebraicComplex)
    (hcycle : theta^k=1) (hpsi : psi≠0) (hroot : psi^4=theta)
    (hparameter : PartialTernaryCubicContext.parameter p f=
      theta^(PartialTernaryCubicContext.charge p f k)) :
    TernaryBundleGauge.cubeRatio
      (PartialTernaryCubicContext.table p (OriginalFourthPowerGauge.twist psi f))=1 := by
  have ht : theta≠0 := by
    intro hz
    rw [hz,zero_pow (Nat.ne_of_gt hk)] at hcycle
    exact zero_ne_one hcycle
  rw [table_twist p hp f psi,SignedBundleGauge.cubeRatio_wordTwist _ psi hpsi,
    hroot]
  change PartialTernaryCubicContext.parameter p f /
    theta^(SignedBundleGauge.signedCharge (AffineThreeFaceDecoder.decoder p) 6)=1
  rw [hparameter,CyclicExponentTransport.nat_pow_eq_zpow hk theta hcycle _ _
    (charge_signed hk p f)]
  exact div_self (zpow_ne_zero _ ht)

theorem exists_gauge (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    {k : ℕ} (hk : 2≤k)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (affine : ∀{n}(f : Signature AlgebraicComplex n),Generated F k f→Affine f)
    (maskScalar : AlgebraicComplex) (hm : maskScalar≠0)
    (mask : Generated F k (fun y=>maskScalar*GeneratedCodeSeven.indicator y)) :
    ∃psi : AlgebraicComplex,psi≠0 ∧ psi^(4*k)=1 ∧
      ∀{n}(f : Signature AlgebraicComplex n),
        (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F→
        ∀p : Word 3→Word n,IsAffineMap p→(∀z,f (p z)≠0)→
          TernaryBundleGauge.cubeRatio
            (PartialTernaryCubicContext.table p (OriginalFourthPowerGauge.twist psi f))=1 := by
  obtain ⟨theta,hcycle,hfaces⟩ := OriginalCubicCommonPhase.common_phase F hF hk
    h0 h1 hX affine maskScalar hm mask
  have ht : theta≠0 := by
    intro hz
    rw [hz,zero_pow (by omega : k≠0)] at hcycle
    exact zero_ne_one hcycle
  obtain ⟨psi,hroot⟩ := CyclicPhaseCharacter.exists_unit_root (Units.mk0 theta ht)
    (by decide : 4≠0)
  have hroot' : (psi : AlgebraicComplex)^4=theta := congrArg Units.val hroot
  refine ⟨psi,psi.ne_zero,?_,?_⟩
  · rw [pow_mul,hroot',hcycle]
  · intro n f hf p hp ha
    exact cubeRatio_twist_eq_one (by omega) p hp f theta psi hcycle psi.ne_zero
      hroot' (hfaces f hf p hp ha)

end
end Paper2.DegreeCSP.OriginalCubicGauge
