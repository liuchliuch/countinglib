import Paper2.Complexity.Interpolation.TargetWeightsMachine

/-! Exact polynomial recovery by the checked target-value machine. -/
namespace Paper2.Complexity.Interpolation.TargetWeights
open Holant.Complexity.BinaryInterpolation
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

theorem basis_eval (z : K) (m : ℕ) (i : Fin (m+1)) :
    (Lagrange.basis Finset.univ
      (fun j : Fin (m+1) => ((j.val+1 : ℕ) : K)) i).eval z =
      numerator z m i / interpolationDenominator
        (fun j : Fin (m+1) => ((j.val+1 : ℕ) : K)) i := by
  simp only [Lagrange.basis,Polynomial.eval_prod,Lagrange.basisDivisor,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_sub,Polynomial.eval_X]
  rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib]
  simp only [div_eq_mul_inv,numerator,interpolationDenominator,mul_comm]

theorem sum_eq_eval (z : K) (m : ℕ) (P : Polynomial K) (hP : P.natDegree ≤ m) :
    (∑i : Fin (m+1), P.eval ((i.val+1 : ℕ) : K) * numerator z m i /
      interpolationDenominator (fun j : Fin (m+1) => ((j.val+1 : ℕ) : K)) i) =
      P.eval z := by
  have hd : P.degree < ((Finset.univ : Finset (Fin (m+1))).card : ℕ) := by
    simp only [Finset.card_univ,Fintype.card_fin]
    calc
      P.degree ≤ (P.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ ≤ (m : WithBot ℕ) := by exact_mod_cast hP
      _ < ((m+1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self m
  have hi : Function.Injective (fun j : Fin (m+1) => ((j.val+1 : ℕ) : K)) :=
    nodes_injective m
  have he := congrArg (fun Q : Polynomial K => Q.eval z)
    (Lagrange.eq_interpolate (s := Finset.univ) (v := fun j : Fin (m+1) =>
      ((j.val+1 : ℕ) : K)) hi.injOn hd)
  simp only [Lagrange.interpolate_apply,Polynomial.eval_finsetSum,
    Polynomial.eval_mul,Polynomial.eval_C,basis_eval] at he
  simpa only [mul_div_assoc] using he.symm

/-- Oracle samples may include the chain scalar gamma^((i+1)*m).  The actual
postprocessor cancels it and evaluates the original polynomial at the fixed
target.  No nonzero-answer hypothesis is used. -/
theorem value_polynomial (gamma z : K) (hgamma : gamma ≠ 0) (m : ℕ)
    (P : Polynomial K) (hP : P.natDegree ≤ m) :
    value gamma z m (fun i => gamma^((i.val+1)*m) *
      P.eval ((i.val+1 : ℕ) : K)) = P.eval z := by
  rw [value_eq_sum gamma z hgamma]
  have hs := sum_eq_eval z m P hP
  rw [←hs]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc,mul_div_mul_left]
  exact pow_ne_zero _ hgamma

end
end Paper2.Complexity.Interpolation.TargetWeights
