import Paper2.DegreeCSP.BooleanQuadratic

/-! Actual conversion of a Boolean quadratic into the manuscript's modulo-four
phase formula. All mixed coefficients are even, and the resulting signature
has the original sign values on every Boolean word. -/
namespace Paper2.DegreeCSP.BooleanQuadraticPhase
open scoped BigOperators
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

def phaseLift : ZMod 2 →+ ZMod 4 where
  toFun a := if a=0 then 0 else 2
  map_zero' := by simp
  map_add' a b := by fin_cases a <;> fin_cases b <;> decide

theorem phaseLift_even (a : ZMod 2) : phaseLift a=0 ∨ phaseLift a=2 := by
  by_cases ha : a=0 <;> simp [phaseLift,ha]

theorem phaseLift_mul_bit (a : ZMod 2) (b : Bool) :
    phaseLift (a*bitValue (ZMod 2) b)=phaseLift a*bitValue (ZMod 4) b := by
  cases b <;> simp

def lift {n : ℕ} (Q : BooleanQuadratic.Polynomial n) : QuadraticPhase n where
  constant := phaseLift Q.constant
  linear i := phaseLift (Q.linear i)
  mixed i j := phaseLift (Q.mixed i j)
  even_mixed i j _ := phaseLift_even (Q.mixed i j)

theorem lift_eval {n : ℕ} (Q : BooleanQuadratic.Polynomial n) (x : Fin n → Bool) :
    (lift Q).eval x=phaseLift (Q.eval x) := by
  simp only [lift,QuadraticPhase.eval,BooleanQuadratic.Polynomial.eval,map_add,map_sum]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact (phaseLift_mul_bit (Q.linear i) (x i)).symm
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i<j
    · simp only [ite_eq_left hij,phaseLift_mul_bit]
    · simp only [ite_eq_right hij,map_zero]

theorem fourthRootPhase_lift (a : ZMod 2) :
    fourthRootPhase (phaseLift a)=(-1 : AlgebraicComplex)^a.val := by
  fin_cases a
  · rfl
  · change imaginaryUnit^2=(-1 : AlgebraicComplex)^1
    simpa only [pow_one] using imaginaryUnit_sq

theorem lift_phase {n : ℕ} (Q : BooleanQuadratic.Polynomial n) (x : Fin n → Bool) :
    fourthRootPhase ((lift Q).eval x)=(-1 : AlgebraicComplex)^(Q.eval x).val := by
  rw [lift_eval,fourthRootPhase_lift]

theorem affine_sign_polynomial {n : ℕ} (Q : BooleanQuadratic.Polynomial n) :
    Affine (fun x => (-1 : AlgebraicComplex)^(Q.eval x).val) := by
  convert affine_formula (1 : AlgebraicComplex) (AffineSystem.unconstrained n) (lift Q) using 1
  funext x
  simp only [affineFormula,AffineSystem.unconstrained_holds,ite_true,one_mul,lift_phase]

theorem affine_sign_of_quadratic {n : ℕ} (P : (Fin n → Bool) → ZMod 2)
    (hP : BooleanQuadratic.Quadratic P) :
    Affine (fun x => (-1 : AlgebraicComplex)^(P x).val) := by
  obtain ⟨Q,hQ⟩ := hP
  have he : (fun x => (-1 : AlgebraicComplex)^(P x).val)=
      (fun x => (-1 : AlgebraicComplex)^(Q.eval x).val) := by
    funext x
    rw [hQ]
  rw [he]
  exact affine_sign_polynomial Q

theorem affine_sign_of_third_coordinate_trivial {n : ℕ} (P : (Fin n → Bool) → ZMod 2)
    (hP : BooleanQuadratic.ThirdCoordinateTrivial P) :
    Affine (fun x => (-1 : AlgebraicComplex)^(P x).val) :=
  affine_sign_of_quadratic P ⟨BooleanQuadratic.polynomial P,BooleanQuadratic.reconstruct P hP⟩

theorem bool_sign (b : Bool) :
    (-1 : AlgebraicComplex)^(bitValue (ZMod 2) b).val=(if b then -1 else 1) := by
  cases b
  · rfl
  · change (-1 : AlgebraicComplex)^1 = -1
    exact pow_one _

theorem affine_boolean_sign {n : ℕ} (P : (Fin n → Bool) → Bool)
    (hP : BooleanQuadratic.Quadratic (fun x => bitValue (ZMod 2) (P x))) :
    Affine (fun x => if P x then (-1 : AlgebraicComplex) else 1) := by
  simpa only [bool_sign] using affine_sign_of_quadratic
    (fun x => bitValue (ZMod 2) (P x)) hP

/-- The same even quadratic phase is valid on any actual affine support,
including an inconsistent system or the empty coordinate set. -/
theorem affine_supported_sign {n : ℕ} (S : AffineSystem n)
    (scale : AlgebraicComplex) (Q : BooleanQuadratic.Polynomial n) :
    Affine (fun x => if S.Holds x then scale*(-1 : AlgebraicComplex)^(Q.eval x).val else 0) := by
  convert affine_formula scale S (lift Q) using 1
  funext x
  simp only [affineFormula,lift_phase]

theorem affine_supported_boolean_sign {n : ℕ} (S : AffineSystem n)
    (scale : AlgebraicComplex) (P : (Fin n → Bool) → Bool)
    (hP : BooleanQuadratic.Quadratic (fun x => bitValue (ZMod 2) (P x))) :
    Affine (fun x => if S.Holds x then scale*(if P x then (-1 : AlgebraicComplex) else 1) else 0) := by
  obtain ⟨Q,hQ⟩ := hP
  have he : (fun x => if S.Holds x then scale*(if P x then (-1 : AlgebraicComplex) else 1) else 0) =
      (fun x => if S.Holds x then scale*(-1 : AlgebraicComplex)^(Q.eval x).val else 0) := by
    funext x
    rw [←hQ,bool_sign]
  rw [he]
  exact affine_supported_sign S scale Q

end
end Paper2.DegreeCSP.BooleanQuadraticPhase
