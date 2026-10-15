import Paper2.Paper1ProvedCriteria
import Holant.Tractable.AffineOperations

/-! Exact affine coefficient reconstruction from an actual coordinate marginal.
The support indicator retains every zero coefficient. Selected coordinates may
be repeated or complemented, and empty coordinate sets are allowed. -/
namespace Paper2.DegreeCSP.AffineCoordinateSubstitution

open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

def word {m n : ℕ} (q : Fin n → Fin m) (flip : Fin n → Bool)
    (x : Fin m → Bool) : Fin n → Bool := fun i => Bool.xor (x (q i)) (flip i)

theorem word_affine {m n : ℕ} (q : Fin n → Fin m) (flip : Fin n → Bool) :
    Holant.Tractable.TwoTranslate.IsAffineMap (word q flip) := by
  intro x y
  funext i
  cases hxi : x (q i) <;> cases hyi : y (q i) <;> cases hfi : flip i <;>
    simp [word,Holant.Tractable.AffinePhase.xor,Holant.Tractable.AffinePhase.origin,
      hxi,hyi,hfi]

theorem affine_precompose {m n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : Affine f) (q : Fin n → Fin m) (flip : Fin n → Bool) :
    Affine (fun x => f (word q flip x)) := by
  apply (Paper1Proved.affine_iff _).mpr
  exact ((Paper1Proved.affine_iff _).mp hf).precompose _ (word_affine q flip)

theorem affine_coordinates {m n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : Affine f) (q : Fin n → Fin m) : Affine (fun x => f (fun i => x (q i))) := by
  convert affine_precompose hf q (fun _ => false) using 1
  funext x
  congr 1
  funext i
  exact (Bool.xor_false (x (q i))).symm

theorem affine_mul {n : ℕ} {f g : Signature AlgebraicComplex n}
    (hf : Affine f) (hg : Affine g) : Affine (fun x => f x*g x) := by
  apply (Paper1Proved.affine_iff _).mpr
  exact ((Paper1Proved.affine_iff _).mp hf).mul ((Paper1Proved.affine_iff _).mp hg)

theorem reconstruct {m n : ℕ} (f support : Signature AlgebraicComplex m)
    (h : Signature AlgebraicComplex n) (hs : Affine support) (hh : Affine h)
    (q : Fin n → Fin m) (flip : Fin n → Bool)
    (he : ∀ x,f x=support x*h (word q flip x)) : Affine f := by
  have ht := affine_mul hs (affine_precompose hh q flip)
  exact (funext he) ▸ ht

/-- The marginal need only agree on the actual nonzero support. Multiplication
by its affine indicator restores all zero entries without a support change. -/
theorem reconstruct_live {m n : ℕ} (f : Signature AlgebraicComplex m)
    (h : Signature AlgebraicComplex n)
    (hs : Affine (fun x => if f x≠0 then (1 : AlgebraicComplex) else 0))
    (hh : Affine h) (q : Fin n → Fin m)
    (hcoeff : ∀ x,f x≠0 → h (fun i => x (q i))=f x) : Affine f := by
  classical
  have ht := affine_mul hs (affine_coordinates hh q)
  convert ht using 1
  funext x
  by_cases hx : f x≠0
  · simp only [ite_eq_left hx,one_mul,hcoeff x hx]
  · simp only [ite_eq_right hx,zero_mul]
    exact not_ne_iff.mp hx

end
end Paper2.DegreeCSP.AffineCoordinateSubstitution
