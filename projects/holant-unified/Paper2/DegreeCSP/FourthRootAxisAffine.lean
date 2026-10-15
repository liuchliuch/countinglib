import Paper2.DegreeCSP.FourthRootClassification
import Paper2.DegreeCSP.BooleanQuadraticPhase

/-! Exact affine formulas for coordinate fourth roots multiplied by a genuine
Boolean quadratic sign. The linear phases retain the original coordinate order,
including the empty coordinate set. -/
namespace Paper2.DegreeCSP.FourthRootAxisAffine
open scoped BigOperators
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

def quadratic {n : ℕ} (q : Fin n → ZMod 4)
    (Q : BooleanQuadratic.Polynomial n) : QuadraticPhase n where
  constant := (BooleanQuadraticPhase.lift Q).constant
  linear i := q i + (BooleanQuadraticPhase.lift Q).linear i
  mixed := (BooleanQuadraticPhase.lift Q).mixed
  even_mixed := (BooleanQuadraticPhase.lift Q).even_mixed

theorem quadratic_eval {n : ℕ} (q : Fin n → ZMod 4)
    (Q : BooleanQuadratic.Polynomial n) (x : Fin n → Bool) :
    (quadratic q Q).eval x =
      (∑ i, q i * bitValue (ZMod 4) (x i)) +
        (BooleanQuadraticPhase.lift Q).eval x := by
  simp only [quadratic, QuadraticPhase.eval, add_mul, Finset.sum_add_distrib]
  ring

theorem phase_sum {ι : Type*} (s : Finset ι) (q : ι → ZMod 4) :
    fourthRootPhase (∑ i ∈ s, q i) = ∏ i ∈ s, fourthRootPhase (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      FourthRootClassification.phase_add, ih]

theorem phase_axis {n : ℕ} (q : Fin n → ZMod 4) (x : Fin n → Bool) :
    fourthRootPhase (∑ i, q i * bitValue (ZMod 4) (x i)) =
      ∏ i, if x i then fourthRootPhase (q i) else 1 := by
  rw [phase_sum]
  apply Finset.prod_congr rfl
  intro i _
  cases hx : x i <;> simp [bitValue, hx]

theorem affine_phase_sign_polynomial {n : ℕ} (c : AlgebraicComplex)
    (q : Fin n → ZMod 4) (Q : BooleanQuadratic.Polynomial n) :
    Affine (fun x => c * (∏ i, if x i then fourthRootPhase (q i) else 1) *
      (-1 : AlgebraicComplex) ^ (Q.eval x).val) := by
  convert affine_formula c (AffineSystem.unconstrained n) (quadratic q Q) using 1
  funext x
  simp only [affineFormula, AffineSystem.unconstrained_holds, ite_true,
    quadratic_eval, FourthRootClassification.phase_add,
    phase_axis, BooleanQuadraticPhase.lift_phase]
  ring

theorem affine_of_fourth_roots {n : ℕ} (c : AlgebraicComplex)
    (φ : Fin n → AlgebraicComplex) (P : (Fin n → Bool) → ZMod 2)
    (hφ : ∀ i, φ i ^ 4 = 1) (hP : BooleanQuadratic.Quadratic P) :
    Affine (fun x => c * (∏ i, if x i then φ i else 1) *
      (-1 : AlgebraicComplex) ^ (P x).val) := by
  classical
  choose q hq using fun i => FourthRootClassification.exists_phase (hφ i)
  obtain ⟨Q, hQ⟩ := hP
  have he : (fun x => c * (∏ i, if x i then φ i else 1) *
      (-1 : AlgebraicComplex) ^ (P x).val) =
      (fun x => c * (∏ i, if x i then fourthRootPhase (q i) else 1) *
        (-1 : AlgebraicComplex) ^ (Q.eval x).val) := by
    funext x
    simp only [hq, hQ]
  rw [he]
  exact affine_phase_sign_polynomial c q Q

theorem affine_boolean_of_fourth_roots {n : ℕ} (c : AlgebraicComplex)
    (φ : Fin n → AlgebraicComplex) (P : (Fin n → Bool) → Bool)
    (hφ : ∀ i, φ i ^ 4 = 1)
    (hP : BooleanQuadratic.Quadratic (fun x => bitValue (ZMod 2) (P x))) :
    Affine (fun x => c * (∏ i, if x i then φ i else 1) *
      (if P x then (-1 : AlgebraicComplex) else 1)) := by
  simpa only [BooleanQuadraticPhase.bool_sign] using
    affine_of_fourth_roots c φ (fun x => bitValue (ZMod 2) (P x)) hφ hP

theorem affine_of_displayed {n : ℕ} (f : Signature AlgebraicComplex n)
    (c : AlgebraicComplex) (φ : Fin n → AlgebraicComplex)
    (P : (Fin n → Bool) → Bool) (hφ : ∀ i, φ i ^ 4 = 1)
    (hP : BooleanQuadratic.Quadratic (fun x => bitValue (ZMod 2) (P x)))
    (hf : ∀ x, f x = c * (∏ i, if x i then φ i else 1) *
      (if P x then (-1 : AlgebraicComplex) else 1)) : Affine f := by
  have he : f = (fun x => c * (∏ i, if x i then φ i else 1) *
      (if P x then (-1 : AlgebraicComplex) else 1)) := funext hf
  rw [he]
  exact affine_boolean_of_fourth_roots c φ P hφ hP

end
end Paper2.DegreeCSP.FourthRootAxisAffine
