import Paper2.DegreeCSP.AffineLiveCoordinates
import Paper2.DegreeCSP.FullSupportProduct

/-! Exact coefficients in the branch where every generated full-support table
is product. An affine support is parametrized by actual original coordinates;
its genuine marginal has one nonzero summand. The resulting unary weights are
retained rather than asserted to be fourth roots or a common family phase. -/
namespace Paper2.DegreeCSP.NoAnchorWeightedSupport
open Tractable AxisRatioSigns
noncomputable section
set_option backward.isDefEq.respectTransparency false

def AllFullSupportProduct (F : SignatureFamily AlgebraicComplex) (k : ℕ) : Prop :=
  ∀ (n : ℕ) (f : Signature AlgebraicComplex n), Generated F k f →
    (∀ x,f x≠0) → Product f

theorem full_support_marginal {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (f : Signature AlgebraicComplex n) (hf : Generated F k f)
    (a : Fin n→Bool) (ha : f a≠0)
    (hxor : BooleanStructure.Preserves BooleanStructure.xor3 {x | f x≠0}) :
    ∃ (r : ℕ) (q : Fin r→Fin n) (h : Signature AlgebraicComplex r),
      Function.Injective q ∧ Generated F k h ∧ (∀ x,h x≠0) ∧
        ∀ x,f x≠0 → h (fun j=>x (q j))=f x := by
  obtain ⟨r,q,hq,hproj⟩ := AffineLiveCoordinates.exists_live_coordinates_xor f a ha hxor
  obtain ⟨h,hh,hhne,hcoeff⟩ :=
    GeneratedCoordinateMarginal.generated_coordinate_marginal f hf q hq hproj
  exact ⟨r,q,h,hq,hh,hhne,hcoeff⟩

theorem parameterization {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hno : AllFullSupportProduct F k)
    (f : Signature AlgebraicComplex n) (hf : Generated F k f)
    (a : Fin n→Bool) (ha : f a≠0)
    (hxor : BooleanStructure.Preserves BooleanStructure.xor3 {x | f x≠0}) :
    ∃ (S : AffineSystem n) (r : ℕ) (q : Fin r→Fin n)
      (h : Signature AlgebraicComplex r),
      Function.Injective q ∧ Generated F k h ∧ (∀ x,h x≠0) ∧ Product h ∧
        (∀ x,S.Holds x ↔ f x≠0) ∧
        (∀ x,f x=if S.Holds x then
          h zeroWord*wordFactor (axisRatio h) (fun j=>x (q j)) else 0) := by
  obtain ⟨r,q,h,hq,hh,hhne,hcoeff⟩ := full_support_marginal f hf a ha hxor
  have hhP : Product h := hno r h hh hhne
  have hnorm := FullSupportProduct.normalized h hhP hhne
  have ht : ∀ x y z : Fin n→Bool,f x≠0 → f y≠0 → f z≠0 →
      f (Holant.Tractable.AffinePhase.xor (Holant.Tractable.AffinePhase.xor x y) z)≠0 :=
    fun x y z hx hy hz => hxor x hx y hy z hz
  obtain ⟨S,_,_,_,_,hS⟩ :=
    Holant.ReedMuller.AffinePatching.exists_support_retraction f a ha ht
  let T : AffineSystem n := (Paper1Proved.affineSystemIso n).symm S
  have hT : ∀ x,T.Holds x ↔ f x≠0 := hS
  refine ⟨T,r,q,h,hq,hh,hhne,hhP,hT,?_⟩
  intro x
  by_cases hx : f x≠0
  · rw [if_pos ((hT x).mpr hx),←hcoeff x hx]
    exact hnorm _
  · rw [if_neg (fun hxS => hx ((hT x).mp hxS))]
    exact not_not.mp hx

end
end Paper2.DegreeCSP.NoAnchorWeightedSupport
