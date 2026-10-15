import Paper2.DegreeCSP.MultiCoordinateContextDegrees
import Paper2.DegreeCSP.FullSupportProduct
import Paper2.DegreeCSP.BooleanSupport

/-! Literal axis copies complete every boundary degree while retaining one
copy of the original compressed table. The resulting full-support table
differs only by nonzero unary factors, so productness returns to its exact
original coefficients. -/
namespace Paper2.DegreeCSP.MultiCoordinateContext
open scoped BigOperators
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable
variable {n r : ℕ} (E : Fin n→Expr r)

def axis (j : Fin r) (i : Fin n) : Expr r:=
  match E i with
  | .inl b=>.inl b
  | .inr (q,b)=>if q=j then .inr (q,b) else .inl b

theorem axis_word (j : Fin r) (x : Fin r→Bool) :
    word (axis E j) x=word E (Function.update (fun _=>false) j (x j)) := by
  funext i
  cases he:E i with
  | inl b=>simp [word,axis,he,eval]
  | inr p=>
    rcases p with ⟨q,b⟩
    by_cases h:q=j
    · simp [word,axis,he,eval,h]
    · simp [word,axis,he,eval,h,Function.update]

theorem axis_boundary_weight (j q : Fin r) (t : ℕ) :
    boundaryWeight (axis E j) t q=if q=j then boundaryWeight E t j else 0 := by
  unfold boundaryWeight
  by_cases h:q=j
  · subst q
    simp only [ite_true]
    apply Finset.sum_congr rfl
    intro i _
    cases he:E i with
    | inl b=>simp [axis,he]
    | inr p=>
      rcases p with ⟨q,b⟩
      by_cases hq:q=j <;> cases b <;> simp [axis,he,hq]
  · simp only [h,ite_false]
    apply Finset.sum_eq_zero
    intro i _
    cases he:E i with
    | inl b=>simp [axis,he]
    | inr p=>
      rcases p with ⟨u,b⟩
      by_cases hu:u=j
      · subst u
        cases b <;> simp [axis,he,Ne.symm h]
      · simp [axis,he,hu]

def padded (f : Signature AlgebraicComplex n) (t : ℕ) :
    Presentation AlgebraicComplex (Fin r):=
  (context E f t).disjointProduct
    (PartialUnaryProducts.product r (fun j=>context (axis E j) f t) (fun _=>t))

theorem padded_value (f : Signature AlgebraicComplex n) {t : ℕ} (ht : 0<t)
    (x : Fin r→Bool) :
    (padded E f t).value x=f (word E x)*
      ∏j,f (word E (Function.update (fun _=>false) j (x j)))^t := by
  rw [padded,Presentation.product_value,PartialUnaryProducts.product_value,value E f ht]
  simp_rw [value _ f ht,axis_word]

theorem padded_boundary_degree (f : Signature AlgebraicComplex n) (t : ℕ) (j : Fin r) :
    (padded E f t).degree (Sum.inl j)=(t+1)*boundaryWeight E t j := by
  rw [padded,Presentation.product_boundary_degree,PartialUnaryProducts.product_boundary_degree]
  rw [Paper2.DegreeCSP.MultiCoordinateContext.boundary_degree E f t j]
  have hd : (∑q:Fin r,t*(context (axis E q) f t).degree (Sum.inl j))=
      t*boundaryWeight E t j := by
    calc
      _=∑q:Fin r,if j=q then t*boundaryWeight E t q else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        rw [Paper2.DegreeCSP.MultiCoordinateContext.boundary_degree (axis E q) f t j,
          axis_boundary_weight]
        by_cases h:j=q <;> simp [h]
      _=t*boundaryWeight E t j := by simp
  rw [hd]
  ring

theorem padded_uses (F : SignatureFamily AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (t : ℕ) : (padded E f t).Uses F :=
  Presentation.product_uses _ _ (uses E F f hf h0 h1 hX t)
    (PartialUnaryProducts.product_uses _ _ _ (fun j=>uses (axis E j) F f hf h0 h1 hX t))

theorem padded_divisible (f : Signature AlgebraicComplex n) (t : ℕ) :
    (padded E f t).DegreeDivisible (t+1) := by
  have hhidden : PartialUnaryProducts.HiddenDivisible (padded E f t) (t+1) :=
    PartialUnaryProducts.product_hidden_divisible _ _
      (hidden_divisible E f t (dvd_refl _))
      (PartialUnaryProducts.product_hidden_divisible_family _ _ _
        (fun j=>hidden_divisible (axis E j) f t (dvd_refl _)))
  rintro (j|h)
  · rw [padded_boundary_degree]
    exact dvd_mul_right _ _
  · exact hhidden h

theorem padded_generated (F : SignatureFamily AlgebraicComplex)
    (f : Signature AlgebraicComplex n)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    {t : ℕ} (ht : 0<t) :
    Generated F (t+1) (fun x=>f (word E x)*
      ∏j,f (word E (Function.update (fun _=>false) j (x j)))^t) := by
  refine ⟨padded E f t,padded_uses E F f hf h0 h1 hX t,padded_divisible E f t,?_⟩
  funext x
  exact padded_value E f ht x

/-- Nonzero axis factors are removed pointwise, with their original signs
and coefficients retained. No positive power is used to recover a root. -/
theorem product_of_padded (f : Signature AlgebraicComplex n) (t : ℕ)
    (live : ∀x,f (word E x)≠0)
    (hp : Product (fun x=>f (word E x)*
      ∏j,f (word E (Function.update (fun _=>false) j (x j)))^t)) :
    Product (fun x=>f (word E x)) := by
  have hi : Product (fun x : Fin r→Bool=>
      ∏j,(f (word E (Function.update (fun _=>false) j (x j)))^t)⁻¹) :=
    BooleanStructure.product_finset Finset.univ
      (fun j x=>(f (word E (Function.update (fun _=>false) j (x j)))^t)⁻¹)
      (fun j _=>product_unary j
        (fun b=>(f (word E (Function.update (fun _=>false) j b))^t)⁻¹))
  convert hp.mul hi using 1
  funext x
  rw [mul_assoc,←Finset.prod_mul_distrib]
  have hone : (∏j:Fin r,
      f (word E (Function.update (fun _=>false) j (x j)))^t*
      (f (word E (Function.update (fun _=>false) j (x j)))^t)⁻¹)=1 := by
    apply Finset.prod_eq_one
    intro j _
    exact mul_inv_cancel₀ (pow_ne_zero t (live _))
  rw [hone,mul_one]

end
end Paper2.DegreeCSP.MultiCoordinateContext

