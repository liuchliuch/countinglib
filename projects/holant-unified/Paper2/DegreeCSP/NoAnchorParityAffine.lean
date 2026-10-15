import Paper2.DegreeCSP.NoAnchorUnaryAffine
import Paper2.DegreeCSP.GeneratedUnaryRestrictions
import Paper2.DegreeCSP.AffineCoordinateSubstitution
import Paper2.DegreeCSP.FourthRootAxisAffine

/-! A concrete generated weighted parity table forces affinity of every
generated table in the no-anchor branch. Actual zero pins expose marginal
axes; their proved unary affinity constrains the exact coefficients. Affine
support indicators then restore all zero entries of the original table. -/
namespace Paper2.DegreeCSP.NoAnchorParityAffine

open Tractable TensorDecomposition AxisRatioSigns
open NoAnchorWeightedSupport NoAnchorWeightedParity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem update_zero_false {n : ℕ} (i : Fin n) :
    Function.update (zeroWord : Fin n → Bool) i false = zeroWord := by
  classical
  funext j
  by_cases h : j=i <;> simp [Function.update,zeroWord,h]

private theorem zero_quadratic (n : ℕ) :
    BooleanQuadratic.Quadratic (fun _ : (Fin n → Bool) => (0 : ZMod 2)) := by
  refine ⟨⟨0,fun _ => 0,fun _ _ => 0⟩,?_⟩
  intro x
  simp [BooleanQuadratic.Polynomial.eval]

/-- The literal unary axes are generated with their original coefficients.
The genuine weighted parity receipt constrains their fourth-power ratios. -/
theorem product_full_support_affine {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hno : AllFullSupportProduct F k) (A B : Bool → AlgebraicComplex) (offset : Bool)
    (hA : ∀ b,A b≠0) (hB : ∀ b,B b≠0)
    (hparity : Generated F k (table A B offset))
    (hp0 : Generated F k (literalPin false))
    (h : Signature AlgebraicComplex n) (hh : Generated F k h)
    (hne : ∀ x,h x≠0) (hp : Product h) : Affine h := by
  classical
  cases n with
  | zero =>
      convert affine_constant 0 (h zeroWord) using 1
      funext x
      exact congrArg h (Subsingleton.elim x zeroWord)
  | succ n =>
      have haxis (i : Fin (n+1)) : axisRatio h i^4=1 := by
        let u : Signature AlgebraicComplex 1 :=
          fun z => h (Function.update zeroWord i (z 0))
        have hu : Generated F k u := generated_unary_axis hh hp0 i
        have hua : Affine u := generated_unary_affine hno A B offset hA hB hparity u hu
        have he := hua.fourth_power_eq ![true] ![false] (hne _) (hne _)
        change h (Function.update zeroWord i true)^4 =
          h (Function.update zeroWord i false)^4 at he
        rw [update_zero_false] at he
        unfold axisRatio
        rw [div_pow,he,div_self (pow_ne_zero 4 (hne zeroWord))]
      have ha := FourthRootAxisAffine.affine_of_fourth_roots
        (h zeroWord) (axisRatio h) (fun _ => (0 : ZMod 2)) haxis (zero_quadratic (n+1))
      simp only [ZMod.val_zero,pow_zero,mul_one] at ha
      convert ha using 1
      funext x
      exact FullSupportProduct.normalized h hp hne x

/-- A bijective coordinate marginal has one actual nonzero summand on every
live fiber. Affinity of that coefficient table and of the support reconstructs
the original table, including zero and nullary signatures. -/
theorem affine_of_support_xor {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hno : AllFullSupportProduct F k) (A B : Bool → AlgebraicComplex) (offset : Bool)
    (hA : ∀ b,A b≠0) (hB : ∀ b,B b≠0)
    (hparity : Generated F k (table A B offset))
    (hp0 : Generated F k (literalPin false))
    (f : Signature AlgebraicComplex n) (hf : Generated F k f)
    (hxor : BooleanStructure.Preserves BooleanStructure.xor3 {x | f x≠0}) : Affine f := by
  classical
  by_cases hz : f=0
  · rw [hz]
    exact affine_zero n
  obtain ⟨a,ha⟩ : ∃ x,f x≠0 := by
    by_contra none
    apply hz
    funext x
    exact not_not.mp (not_exists.mp none x)
  obtain ⟨r,q,h,hq,hh,hne,hcoeff⟩ := full_support_marginal f hf a ha hxor
  have hp : Product h := hno r h hh hne
  have hhA : Affine h := product_full_support_affine hno A B offset hA hB hparity hp0
    h hh hne hp
  have hs : Affine (fun x => if f x≠0 then (1 : AlgebraicComplex) else 0) := by
    convert BooleanStructure.affine_indicator_of_xor {x | f x≠0} hxor using 1
    funext x
    by_cases hx : f x≠0 <;> simp [BooleanStructure.indicator,hx]
  exact AffineCoordinateSubstitution.reconstruct_live f h hs hhA q hcoeff

/-- Actual original-table BO supplies the required affine support. The sole
extra branch resource is the concrete generated weighted parity table. -/
theorem generated_affine {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hk : 0<k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (hno : AllFullSupportProduct F k) (A B : Bool → AlgebraicComplex) (offset : Bool)
    (hA : ∀ b,A b≠0) (hB : ∀ b,B b≠0)
    (hparity : Generated F k (table A B offset))
    (hp0 : Generated F k (literalPin false))
    (f : Signature AlgebraicComplex n) (hf : Generated F k f) : Affine f :=
  affine_of_support_xor hno A B offset hA hB hparity hp0 f hf
    (BooleanGeneratedAffineSupport.generated_support_xor F hk hX hBO f hf)

end
end Paper2.DegreeCSP.NoAnchorParityAffine

