import Paper2.Paper1ProvedOddUnaryOneHotBinaryProjectionPolynomial
import Paper2.Paper1ProvedOddUnaryOneHotBinaryProjectionFactors
import Holant.Signature
namespace Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type} [Field K]
private def deltaWord (v : Bool → Bool) : Tensor K Bool :=
  fun x => if x=v then 1 else 0

private theorem encode_deltaWord (v : Bool → Bool) :
    Polynomial.encode (deltaWord (K:=K) v)=MvPolynomial.monomial (Polynomial.exponent v) 1 := by
  classical
  simp [Polynomial.encode,deltaWord,apply_ite]

private theorem encode_sum {ι τ : Type} [Fintype ι] [Fintype τ]
    (f : τ → Tensor K ι) :
    Polynomial.encode (fun x => ∑ i : τ,f i x)=∑ i : τ,Polynomial.encode (f i) := by
  classical
  simp only [Polynomial.encode,map_sum]
  rw [Finset.sum_comm]

private theorem rename_two_monomial {σ : Type} (i j : Bool) :
    MvPolynomial.rename (Sum.inl : Bool → Bool ⊕ σ)
      (MvPolynomial.monomial (Polynomial.exponent (fun b => if b then j else i)) (1:K))=
    (if i then MvPolynomial.X (.inl false) else 1)*
    (if j then MvPolynomial.X (.inl true) else 1) := by
  classical
  rw [MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Polynomial.exponent_apply,Fintype.prod_bool,MvPolynomial.C_1,one_mul,
    map_mul,map_pow,MvPolynomial.rename_X]
  cases i <;> cases j <;> simp
  all_goals ring

/-- The four conditional coefficient polynomials reconstruct the entire
generating polynomial, with the retained port order fixed explicitly. -/
theorem encode_twoPort_matrix {σ : Type} [Fintype σ] (f : Tensor K (Bool ⊕ σ)) :
    Polynomial.encode f=twoPortPolynomial (fun i j =>
      Polynomial.encode (fun y => f (Sum.elim (fun b => if b then j else i) y))) := by
  classical
  have expansion : f=fun x => ∑ v : Bool → Bool,
      deltaWord v (fun b => x (.inl b))*
      f (Sum.elim v (fun i => x (.inr i))) := by
    funext x
    simp only [deltaWord,ite_mul,one_mul,zero_mul]
    simp
    congr 1
    funext i
    cases i <;> rfl
  conv_lhs => rw [expansion,encode_sum]
  have product_eq (v : Bool → Bool) :
      Polynomial.encode (fun x : (Bool ⊕ σ) → Bool =>
        deltaWord v (fun b => x (.inl b))*f (Sum.elim v (fun i => x (.inr i))))=
      MvPolynomial.rename Sum.inl (Polynomial.encode (deltaWord v))*
        MvPolynomial.rename Sum.inr (Polynomial.encode (fun y => f (Sum.elim v y))) :=
    Polynomial.encode_tensor_product (deltaWord v) (fun y => f (Sum.elim v y))
  simp_rw [product_eq,encode_deltaWord]
  let term : (Bool → Bool) → MvPolynomial (Bool ⊕ σ) K := fun v =>
    MvPolynomial.rename Sum.inl (MvPolynomial.monomial (Polynomial.exponent v) 1)*
    MvPolynomial.rename Sum.inr (Polynomial.encode (fun y => f (Sum.elim v y)))
  change (∑ v : Bool → Bool,term v)=_
  have enumeration : (∑ v : Bool → Bool,term v)=
      ∑ i : Bool,∑ j : Bool,term ((Equiv.boolArrowEquivProd Bool).symm (i,j)) := by
    simpa only [Fintype.sum_prod_type] using
      ((Equiv.boolArrowEquivProd Bool).symm.sum_comp term).symm
  rw [enumeration]
  have arrow (i j : Bool) : (Equiv.boolArrowEquivProd Bool).symm (i,j)=
      fun b => if b then j else i := by
    funext b
    cases b <;> rfl
  simp only [Fintype.sum_bool,term,arrow,
    rename_two_monomial,twoPortPolynomial]
  simp only [Bool.false_eq_true,ite_false,ite_true,one_mul,mul_one]
  ring

end
end Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection
