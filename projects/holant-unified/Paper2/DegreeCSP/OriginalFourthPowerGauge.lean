import Paper2.DegreeCSP.OriginalContextCommonPhase
import Paper2.DegreeCSP.TwoWordContextPhaseBalance

/-! One actual algebraic weight gauge is chosen for every original language
member. It is derived from all original live-row contexts and their degree
cycles. The conclusion controls fourth powers of the original coefficients;
quadratic phase structure is a separate proof obligation. -/
namespace Paper2.DegreeCSP.OriginalFourthPowerGauge
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false

def twist {n : ℕ} (psi : AlgebraicComplex) (f : Signature AlgebraicComplex n) :
    Signature AlgebraicComplex n := fun x=>f x*psi⁻¹^(Paper2.weight x)

theorem twist_support {n : ℕ} (psi : AlgebraicComplex) (hpsi : psi≠0)
    (f : Signature AlgebraicComplex n) (x : Fin n→Bool) :
    twist psi f x≠0 ↔ f x≠0 := by
  have hp : psi⁻¹^(Paper2.weight x)≠0 := pow_ne_zero _ (inv_ne_zero hpsi)
  constructor
  · exact fun h=>(mul_ne_zero_iff.mp h).1
  · exact fun h=>mul_ne_zero h hp

/-- All original nonzero coefficients become fourth-root relatives under
one common weight twist; the chosen phase has order dividing 4k. -/
theorem exists_gauge (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    {k : ℕ} (hk : 0<k)
    (hp0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (hp1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (unary : ∀g : Signature AlgebraicComplex 1,Generated F k g→Affine g) :
    ∃psi : AlgebraicComplex,psi≠0 ∧ psi^(4*k)=1 ∧
      ∀{n : ℕ}(f : Signature AlgebraicComplex n),
        (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F→∀x y,
        f x≠0→f y≠0→(twist psi f y/twist psi f x)^4=1 := by
  obtain ⟨theta,hcycle,hratio⟩ :=
    OriginalContextCommonPhase.common_phase F hF hk hp0 hp1 hX unary
  have htheta : theta≠0 := by
    intro he
    rw [he,zero_pow (Nat.ne_of_gt hk)] at hcycle
    exact zero_ne_one hcycle
  obtain ⟨psi,hroot⟩ := CyclicPhaseCharacter.exists_unit_root (Units.mk0 theta htheta)
    (by decide : 4≠0)
  have hroot' : (psi : AlgebraicComplex)^4=theta := congrArg Units.val hroot
  refine ⟨psi,psi.ne_zero,?_,?_⟩
  · rw [pow_mul,hroot',hcycle]
  · intro n f hf x y hx hy
    exact TwoWordContext.ratio_four_weight_twist x y hk theta psi (f x) (f y)
      hcycle hroot' hx hy (hratio f hf x y hx hy)

/-- The ratios assertion equivalently preserves one fourth power over the
whole nonzero support of each original table. -/
theorem fourth_power_eq {n : ℕ} (psi : AlgebraicComplex) (hpsi : psi≠0)
    (f : Signature AlgebraicComplex n) (x y : Fin n→Bool)
    (hx : f x≠0) (_hy : f y≠0)
    (h : (twist psi f y/twist psi f x)^4=1) :
    twist psi f y^4=twist psi f x^4 := by
  have htx := (twist_support psi hpsi f x).mpr hx
  have hpow : twist psi f x^4≠0 := pow_ne_zero 4 htx
  rw [div_pow] at h
  exact (div_eq_one_iff_eq hpow).mp h

end
end Paper2.DegreeCSP.OriginalFourthPowerGauge
