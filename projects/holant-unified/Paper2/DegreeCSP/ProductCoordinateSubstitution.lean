import Paper2.Tractable.Product

/-! Literal product factors survive selected, repeated and complemented
coordinates. Support reconstruction is an exact pointwise multiplication. -/
namespace Paper2.DegreeCSP.ProductCoordinateSubstitution
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

def word {m n : ℕ} (q : Fin n→Fin m) (flip : Fin n→Bool) (x : Fin m→Bool) : Fin n→Bool :=
  fun i=>Bool.xor (x (q i)) (flip i)

private theorem unary_nonzero (u : Bool→AlgebraicComplex) (hu : u≠0) (b : Bool) :
    (fun z=>u (Bool.xor z b))≠0 := by
  intro h
  apply hu
  funext z
  have hz := congrFun h (Bool.xor z b)
  cases z <;> cases b <;> simpa using hz

def factor {m n : ℕ} (q : Fin n→Fin m) (flip : Fin n→Bool) : ProductFactor n→ProductFactor m
  | .unary i u hu => .unary (q i) (fun z=>u (Bool.xor z (flip i))) (unary_nonzero u hu (flip i))
  | .equality i j => if flip i=flip j then .equality (q i) (q j) else .disequality (q i) (q j)
  | .disequality i j => if flip i=flip j then .disequality (q i) (q j) else .equality (q i) (q j)

theorem factor_eval {m n : ℕ} (q : Fin n→Fin m) (flip : Fin n→Bool)
    (f : ProductFactor n) (x : Fin m→Bool) :
    (factor q flip f).eval x=f.eval (word q flip x) := by
  cases f with
  | unary i u hu => rfl
  | equality i j =>
    cases hi:flip i <;> cases hj:flip j <;> cases hxi:x (q i) <;> cases hxj:x (q j) <;>
      simp [factor,ProductFactor.eval,word,Signature.equality,Signature.disequality,hi,hj,hxi,hxj]
  | disequality i j =>
    cases hi:flip i <;> cases hj:flip j <;> cases hxi:x (q i) <;> cases hxj:x (q j) <;>
      simp [factor,ProductFactor.eval,word,Signature.equality,Signature.disequality,hi,hj,hxi,hxj]

theorem formula {m n : ℕ} (q : Fin n→Fin m) (flip : Fin n→Bool)
    (c : AlgebraicComplex) (fs : List (ProductFactor n)) :
    productFormula c (fs.map (factor q flip))=fun x=>productFormula c fs (word q flip x) := by
  funext x
  simp only [productFormula,List.map_map,Function.comp_def,factor_eval]

/-- Repetition and complementation retain every literal unary and binary
factor, including inconsistent repeated constraints and empty products. -/
theorem product_precompose {m n : ℕ} {f : Signature AlgebraicComplex n} (hf : Product f)
    (q : Fin n→Fin m) (flip : Fin n→Bool) : Product (fun x=>f (word q flip x)) := by
  rcases hf with rfl|⟨c,hc,fs,rfl⟩
  · exact product_zero m
  · rw [←formula]
    exact product_formula c _

theorem product_coordinates {m n : ℕ} {f : Signature AlgebraicComplex n} (hf : Product f)
    (q : Fin n→Fin m) : Product (fun x=>f (fun i=>x (q i))) := by
  convert product_precompose hf q (fun _=>false) using 1
  funext x
  congr 1
  funext i
  exact (Bool.xor_false (x (q i))).symm

/-- A product support indicator and a product parameter table reconstruct
the original coefficients exactly when the parameter word agrees on support. -/
theorem reconstruct {m n : ℕ} (f : Signature AlgebraicComplex m)
    (support : Signature AlgebraicComplex m) (h : Signature AlgebraicComplex n)
    (hs : Product support) (hh : Product h) (q : Fin n→Fin m) (flip : Fin n→Bool)
    (hform : ∀x,f x=support x*h (word q flip x)) : Product f := by
  have hp := hs.mul (product_precompose hh q flip)
  convert hp using 1
  funext x
  exact hform x

/-- An exact coordinate marginal needs to agree only on the live support.
The actual support indicator restores every zero coefficient. -/
theorem reconstruct_live {m n : ℕ} (f : Signature AlgebraicComplex m)
    (h : Signature AlgebraicComplex n)
    (hs : Product (fun x=>if f x≠0 then (1 : AlgebraicComplex) else 0))
    (hh : Product h) (q : Fin n→Fin m)
    (hcoeff : ∀x,f x≠0→h (fun i=>x (q i))=f x) : Product f := by
  classical
  have hp := hs.mul (product_coordinates hh q)
  convert hp using 1
  funext x
  by_cases hx:f x≠0
  · simp only [if_pos hx,one_mul,hcoeff x hx]
  · simp only [if_neg hx,zero_mul]
    exact not_ne_iff.mp hx

end
end Paper2.DegreeCSP.ProductCoordinateSubstitution
