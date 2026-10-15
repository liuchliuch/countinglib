import Paper2.Paper1ProvedOddUnaryOneHotBinaryProjectionFactors

/-! Specialization stays inside the original infinite coefficient field. -/
namespace Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection
noncomputable section
open MvPolynomial
variable {K : Type} [Field K] [Infinite K]

private theorem zero_of_eval_zero_fin {n : ℕ} (p : MvPolynomial (Fin n) K)
    (zero : ∀ x,eval x p=0) : p=0 := by
  induction n with
  | zero =>
      apply (isEmptyRingEquiv K (Fin 0)).injective
      have scalar := zero 0
      rw [eval_zero] at scalar
      change p.coeff 0=0 at scalar
      simpa only [map_zero,isEmptyRingEquiv_eq_coeff_zero] using scalar
  | succ n ih =>
      have mapped : ∀ x : Fin n → K,
          Polynomial.map (eval x) (finSuccEquiv K n p)=0 := by
        intro x
        apply Polynomial.zero_of_eval_zero
        intro z
        rw [←eval_eq_eval_mv_eval']
        exact zero (Fin.cons z x)
      apply (finSuccEquiv K n).injective
      rw [map_zero]
      apply Polynomial.ext
      intro k
      apply ih
      intro x
      have coefficient := congrArg (fun q => Polynomial.coeff q k) (mapped x)
      simpa only [Polynomial.coeff_map,Polynomial.coeff_zero] using coefficient

/-- Evaluation on the original infinite field determines a multivariate
polynomial with finitely many variables. -/
theorem zero_of_eval_zero {σ : Type} [Fintype σ] (p : MvPolynomial σ K)
    (zero : ∀ x,eval x p=0) : p=0 := by
  classical
  let e := Fintype.equivFin σ
  apply (renameEquiv K e).injective
  rw [map_zero]
  apply zero_of_eval_zero_fin
  intro x
  simpa only [renameEquiv_apply,eval_rename] using zero (x ∘ e)

/-- Simultaneous nonvanishing is achieved by a specialization in `K` itself.
This applies to the determinant and the desired visible binary entry or
linear functional, without adjoining algebraic coefficients. -/
theorem exists_common_nonvanishing {σ : Type} [Fintype σ]
    (p q : MvPolynomial σ K) (pnz : p≠0) (qnz : q≠0) :
    ∃ z : σ → K,eval z p≠0 ∧ eval z q≠0 := by
  classical
  by_contra bad
  push Not at bad
  have product_zero : p*q=0 := by
    apply zero_of_eval_zero
    intro z
    rw [map_mul]
    by_cases pzero : eval z p=0
    · rw [pzero,zero_mul]
    · rw [bad z pzero,mul_zero]
  exact (mul_ne_zero pnz qnz) product_zero

def matrixDeterminantPolynomial {σ : Type} (M : Bool → Bool → MvPolynomial σ K) :
    MvPolynomial σ K := M false false*M true true-M false true*M true false

def matrixVisiblePolynomial {σ : Type} (w : Bool → Bool → K)
    (M : Bool → Bool → MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ i : Bool,∑ j : Bool,C (w i j)*M i j

/-- Visibility of an actual tensor coefficient proves that the associated
linear-expression polynomial is nonzero. -/
theorem matrixVisiblePolynomial_nonzero {σ : Type}
    (M : Bool → Bool → MvPolynomial σ K) (w : Bool → Bool → K)
    (visible : ∃ d : σ →₀ ℕ,
      (∑ i : Bool,∑ j : Bool,w i j*(M i j).coeff d)≠0) :
    matrixVisiblePolynomial w M≠0 := by
  obtain ⟨d,live⟩ := visible
  intro zero
  apply live
  have coefficient := congrArg (fun p : MvPolynomial σ K => p.coeff d) zero
  simpa only [matrixVisiblePolynomial,coeff_sum,coeff_C_mul,
    AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using coefficient

/-- A polynomial binary matrix can be specialized over the original field
while preserving its determinant and any specified visible linear expression. -/
theorem select_polynomial_matrix {σ : Type} [Fintype σ]
    (M : Bool → Bool → MvPolynomial σ K) (w : Bool → Bool → K)
    (nonsingular : matrixDeterminantPolynomial M≠0)
    (visible : matrixVisiblePolynomial w M≠0) :
    ∃ z : σ → K,
      determinant (fun i j => eval z (M i j))≠0 ∧
      (∑ i : Bool,∑ j : Bool,w i j*eval z (M i j))≠0 := by
  obtain ⟨z,det,live⟩ := exists_common_nonvanishing
    (matrixDeterminantPolynomial M) (matrixVisiblePolynomial w M) nonsingular visible
  refine ⟨z,?_,?_⟩
  · simpa only [matrixDeterminantPolynomial,determinant,map_sub,map_mul] using det
  · simpa only [matrixVisiblePolynomial,map_sum,map_mul,eval_C] using live

end
end Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection

