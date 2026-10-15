import Paper2.Paper1ProvedOddUnaryJordanChain
import Holant.Complexity.BinaryInterpolation.NormalizedQueries

/-! Exact Lagrange recovery of ordinary Jordan queries, and the full unary
span in the original coefficient field. Runtime code is a separate leaf. -/
namespace Paper2.Paper1Proved.OddUnary.JordanInterpolation
open Holant Holant.Tractable Holant.Complexity.BinaryInterpolation
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] {m n : ℕ}

def evalWeight (nodes : Fin (m+1) → K) (z : K) (i : Fin (m+1)) : K :=
  (∏ j ∈ Finset.univ.erase i,(z-nodes j))/interpolationDenominator nodes i

def recoverEval (nodes : Fin (m+1) → K) (z : K) (values : Fin (m+1) → K) : K :=
  ∑ i,values i*evalWeight nodes z i

theorem evalWeight_basis (nodes : Fin (m+1) → K) (z : K) (i : Fin (m+1)) :
    evalWeight nodes z i=(Lagrange.basis Finset.univ nodes i).eval z := by
  simp only [evalWeight,interpolationDenominator,Lagrange.basis,Lagrange.basisDivisor,
    Polynomial.eval_prod,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_sub,Polynomial.eval_X]
  rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib]
  exact div_eq_mul_inv _ _ |>.trans (mul_comm _ _)

theorem recoverEval_polynomial (nodes : Fin (m+1) → K) (hi : Function.Injective nodes)
    (P : Polynomial K) (hP : P.natDegree≤m) (z : K) :
    recoverEval nodes z (fun i => P.eval (nodes i))=P.eval z := by
  have hd : P.degree < ((Finset.univ : Finset (Fin (m+1))).card : ℕ) := by
    simp only [Finset.card_univ,Fintype.card_fin]
    calc
      P.degree ≤ (P.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ ≤ (m : WithBot ℕ) := by exact_mod_cast hP
      _ < ((m+1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self m
  have hp := Lagrange.eq_interpolate (s:=Finset.univ) (v:=nodes) hi.injOn hd
  have he := congrArg (fun p : Polynomial K => p.eval z) hp
  simpa only [Lagrange.interpolate_apply,Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_C,←evalWeight_basis,recoverEval] using he.symm

theorem network_eval_interpolation (N : Holant.Network K n) (S : Finset (Fin N.shape.vertices))
    (L R : (v : Fin N.shape.vertices) → Holant.Signature K (N.shape.arity v))
    (x : Fin n → Bool) (nodes : Fin (S.card+1) → K) (hi : Function.Injective nodes) (z : K) :
    recoverEval nodes z (fun i => (pencilNetwork N S L R (nodes i)).denote x)=
      (pencilNetwork N S L R z).denote x := by
  have h := recoverEval_polynomial nodes hi (networkPolynomial N S L R x)
    (networkPolynomial_degree N S L R x) z
  simpa only [networkPolynomial_eval] using h

/-- Every query normalization divides only a proved nonzero fixed scalar
power; graph values may be zero or cancel. -/
theorem normalized_query_recovery_eval (N : Holant.Network K n)
    (S : Finset (Fin N.shape.vertices))
    (L R : (v : Fin N.shape.vertices) → Holant.Signature K (N.shape.arity v))
    (nodes c : Fin (S.card+1) → K)
    (Q : Fin (S.card+1) → (v : Fin N.shape.vertices) → Holant.Signature K (N.shape.arity v))
    (hi : Function.Injective nodes) (hc : ∀ i,c i≠0)
    (hQ : ∀ i,∀ v∈S,∀ x,Q i v x=c i*(L v x+nodes i*R v x))
    (x : Fin n → Bool) (z : K) :
    recoverEval nodes z (fun i => (queryNetwork N S (Q i)).denote x/(c i)^S.card)=
      (pencilNetwork N S L R z).denote x := by
  have he : (fun i => (queryNetwork N S (Q i)).denote x/(c i)^S.card)=
      (fun i => (pencilNetwork N S L R (nodes i)).denote x) := by
    funext i
    rw [queryNetwork_value N S L R (Q i) (c i) (nodes i) (hQ i) x]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ (hc i))
  rw [he]
  exact network_eval_interpolation N S L R x nodes hi z

section UnarySpan
variable {s : ℕ} {a : ℕ → ℕ} {H : (i : Fin s) → Holant.Signature K (a i.val)}
variable {phi : K →+* AlgebraicComplex}
variable (J : NRCanonical.JordanReceipt (H := H) phi)

def leftCoefficient (v : Bool → K) : K := (v false-v true/J.ratioK)/J.eigenvalueK
def rightCoefficient (v : Bool → K) : K := v true/(J.defectK*J.ratioK)

theorem unary_span (injective : Function.Injective phi) (v : Bool → K) :
    (fun x : Fin 1 → Bool => v (x 0))=fun x =>
      leftCoefficient J v*JordanChain.left J x+rightCoefficient J v*JordanChain.right J x := by
  have ht : J.ratioK≠0 := NRJordanPowers.repeated_true_nonzero _ (J.ratioK_square injective)
  funext x
  cases h : x 0 <;> simp only [h,leftCoefficient,rightCoefficient,JordanChain.left,JordanChain.right,
    ite_true,ite_false,Bool.false_eq_true]
  all_goals field_simp [J.eigenvalueK_nonzero,J.defectK_nonzero,ht]
  all_goals ring

theorem unary_pencil (injective : Function.Injective phi) (v : Bool → K)
    (h : leftCoefficient J v≠0) :
    (fun x : Fin 1 → Bool => v (x 0))=fun x => leftCoefficient J v*
      (JordanChain.left J x+(rightCoefficient J v/leftCoefficient J v)*JordanChain.right J x) := by
  rw [unary_span J injective v]
  funext x
  field_simp [h]

theorem unary_top (injective : Function.Injective phi) (v : Bool → K)
    (h : leftCoefficient J v=0) :
    (fun x : Fin 1 → Bool => v (x 0))=fun x => rightCoefficient J v*JordanChain.right J x := by
  rw [unary_span J injective v]
  simp only [h,zero_mul,zero_add]

end UnarySpan
end
end Paper2.Paper1Proved.OddUnary.JordanInterpolation
