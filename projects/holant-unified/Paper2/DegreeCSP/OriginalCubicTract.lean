import Paper2.DegreeCSP.AffineCubicRecovery
import Paper2.DegreeCSP.OriginalFourthPowerGauge
import Paper2.DegreeCSP.MixedGaugeToTract

/-! One common weight twist with the actual live three-face equations gives
one shared original diagonal affine chart. No root order, generated decoder,
or powered coefficient table substitutes for the original signatures here. -/
namespace Paper2.DegreeCSP.OriginalCubicTract
open scoped BigOperators
open Tractable
open Holant.Tractable.AffinePhase (Word)
open Holant.Tractable.TwoTranslate (IsAffineMap)
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem affine_twist_of_live_cubes {n : ℕ} (psi : AlgebraicComplex) (hpsi : psi≠0)
    (f : Signature AlgebraicComplex n)
    (hxor : BooleanStructure.Preserves BooleanStructure.xor3 {x | f x≠0})
    (cubes : ∀p : Word 3→Word n,IsAffineMap p→(∀x,f (p x)≠0)→
      TernaryBundleGauge.cubeRatio
        (AffineCubicRecovery.cubeTable (OriginalFourthPowerGauge.twist psi f) p)=1) :
    Affine (OriginalFourthPowerGauge.twist psi f) := by
  apply AffineCubicRecovery.affine_of_live_cubes
  · have hs : {x | OriginalFourthPowerGauge.twist psi f x≠0}={x | f x≠0} := by
      ext x
      exact OriginalFourthPowerGauge.twist_support psi hpsi f x
    rw [hs]
    exact hxor
  · intro p hp live
    exact cubes p hp (fun x=>(OriginalFourthPowerGauge.twist_support psi hpsi f _).mp (live x))

theorem weight_factor {n : ℕ} (a : AlgebraicComplex) (x : Word n) :
    a^(Paper2.weight x)=∏i,if x i then a else 1 := by
  unfold Paper2.weight
  rw [←Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> simp

theorem shared_diagonal_affine (F : SignatureFamily AlgebraicComplex)
    (psi : AlgebraicComplex) (hpsi : psi≠0)
    (hxor : ∀f∈F,BooleanStructure.Preserves BooleanStructure.xor3 {x | f.2 x≠0})
    (cubes : ∀f∈F,∀p : Word 3→Word f.1,IsAffineMap p→(∀x,f.2 (p x)≠0)→
      TernaryBundleGauge.cubeRatio
        (AffineCubicRecovery.cubeTable (OriginalFourthPowerGauge.twist psi f.2) p)=1) :
    ClassesToTract.SharedDiagonalAffine F := by
  apply MixedGaugeToTract.shared_diagonal_affine F (a:=1) (b:=psi⁻¹)
    one_ne_zero (inv_ne_zero hpsi) 1
  intro f hf
  have ht := affine_twist_of_live_cubes psi hpsi f.2 (hxor f hf) (cubes f hf)
  convert ht using 1
  funext x
  simp only [MixedGaugeToTract.gauge,pow_one,OriginalFourthPowerGauge.twist,weight_factor]

theorem tract_family (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    (psi : AlgebraicComplex) (hpsi : psi≠0)
    (hxor : ∀f∈F,BooleanStructure.Preserves BooleanStructure.xor3 {x | f.2 x≠0})
    (cubes : ∀f∈F,∀p : Word 3→Word f.1,IsAffineMap p→(∀x,f.2 (p x)≠0)→
      TernaryBundleGauge.cubeRatio
        (AffineCubicRecovery.cubeTable (OriginalFourthPowerGauge.twist psi f.2) p)=1) :
    Tract (familyAction sourceKBasis F) :=
  ClassesToTract.diagonal_affine_family F hF (shared_diagonal_affine F psi hpsi hxor cubes)

end
end Paper2.DegreeCSP.OriginalCubicTract
