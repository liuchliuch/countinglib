import Paper2.DegreeCSP.NoAnchorWeightedParity
import Paper2.DegreeCSP.FourthRootClassification

/-! The genuine parity marginal constraint closes all unary affine cases,
including zero and either one-point support. -/
namespace Paper2.DegreeCSP.NoAnchorWeightedParity
open Tractable TensorDecomposition NoAnchorWeightedSupport
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem affine_literalPin (b : Bool) : Affine (literalPin b) := by
  let S : AffineSystem 1 := ⟨1,fun _ _=>1,fun _=>bitValue (ZMod 2) b⟩
  have hs (x : Fin 1→Bool) : S.Holds x↔x 0=b := by
    simp only [AffineSystem.Holds,S,Fin.sum_univ_one,one_mul,Fin.forall_fin_one]
    cases hx:x 0 <;> cases b <;> decide
  convert affine_indicator S using 1
  funext x
  simp only [literalPin,hs]

theorem unary_affine_of_fourth_ratio (u : Signature AlgebraicComplex 1)
    (h0 : u ![false]≠0) (h4 : (u ![true]/u ![false])^4=1) : Affine u := by
  obtain ⟨q,hq⟩ := FourthRootClassification.exists_phase h4
  let Q : QuadraticPhase 1 := ⟨0,fun _=>q,fun _ _=>0,fun _ _ _=>Or.inl rfl⟩
  convert affine_formula (u ![false]) (AffineSystem.unconstrained 1) Q using 1
  funext x
  have hw : x=![x 0] := by funext i;rw [Fin.eq_zero i];rfl
  rw [hw]
  cases hx:x 0
  · simp [affineFormula,QuadraticPhase.eval,Q]
  · simpa [affineFormula,QuadraticPhase.eval,Q,hq] using
      (mul_div_cancel₀ (u ![true]) h0).symm

/-- Every actual unary is either a scaled literal pin or has a fourth-root
ratio. The parity face proves the stronger square-ratio constraint internally. -/
theorem generated_unary_affine {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hno : AllFullSupportProduct F k) (A B : Bool→AlgebraicComplex) (offset : Bool)
    (hA : ∀b,A b≠0) (hB : ∀b,B b≠0)
    (hf : Generated F k (table A B offset))
    (u : Signature AlgebraicComplex 1) (hu : Generated F k u) : Affine u := by
  classical
  by_cases h0:u ![false]=0
  · have hp := (affine_literalPin true).scale (u ![true])
    convert hp using 1
    funext x
    have hw : x=![x 0] := by funext i;rw [Fin.eq_zero i];rfl
    rw [hw]
    cases x 0 <;> simp [literalPin,h0]
  by_cases h1:u ![true]=0
  · have hp := (affine_literalPin false).scale (u ![false])
    convert hp using 1
    funext x
    have hw : x=![x 0] := by funext i;rw [Fin.eq_zero i];rfl
    rw [hw]
    cases x 0 <;> simp [literalPin,h1]
  have hsq := generated_unary_square hno A B offset hA hB hf u hu
    (fun b=>by cases b;exact h0;exact h1)
  have hr2 : (u ![true]/u ![false])^2=1 := by
    rw [div_pow,←hsq,div_self (pow_ne_zero 2 h0)]
  apply unary_affine_of_fourth_ratio u h0
  calc
    (u ![true]/u ![false])^4=((u ![true]/u ![false])^2)^2 := by ring
    _=1 := by rw [hr2];norm_num

end
end Paper2.DegreeCSP.NoAnchorWeightedParity
