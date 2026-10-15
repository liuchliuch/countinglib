import Paper2.ExactInput.FixedRootCodec.SturmCounterMachines
import Paper2.ExactInput.FixedRootCodec.VariableRootBisectionCoverage

/-! The concrete squarefree/Euclidean/sign program computes the exact
number of distinct real roots at or below a rational query. The lower
endpoint is a computed Cauchy point for the original input polynomial.
All inputs, including zero and constants, are covered. -/
namespace Paper2.ExactInput.FixedRootCodec.SturmCounter
open Computability Paper2.Algebraic Paper2.Complexity Polynomial
open BinaryCompose FixedFieldMachines BellMachines VariablePolynomial
noncomputable section

theorem doubledVariation_constant {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0)
    (hdegree : (polynomial v).natDegree=0) (q : ℚ) : doubledVariation v q=0 := by
  have h : (doubledVariation v q : ℝ)=0 := by
    rw [doubledVariation_real,generatedDoubledVariation_constant v hv hdegree]
    simp
  exact Rat.cast_eq_zero.mp h

theorem cauchy_root_filter {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0) (q : ℚ) :
    (((polynomial v).map (algebraMap ℚ ℝ)).roots.toFinset.filter
      fun r => (VariableCauchyPoint.farLeft v q : ℝ) < r ∧ r ≤ (q : ℝ)) =
    ((VariableRootBisection.realRootSet v).filter fun r => r ≤ (q : ℝ)) := by
  classical
  change (VariableRootBisection.realRootSet v).filter _ = _
  apply Finset.filter_congr
  intro r hr
  have hp : polynomial v ≠ 0 := (polynomial_eq_zero_iff v).not.mpr hv
  have hz := (VariableRootBisection.realRootSet_mem_iff v hp r).mp hr
  have hl := VariableCauchyPoint.farLeft_lt_realRoot v q hp r hz
  exact and_iff_right hl

theorem rationalCount_correct {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0) (q : ℚ) :
    rationalCount v q=(VariableRootBisection.realRootCount v q : ℚ) := by
  classical
  by_cases hdegree : (polynomial (squarefreeVector v)).natDegree=0
  · have hd : derivative (squarefreeVector v)=0 := by
      apply (polynomial_eq_zero_iff _).mp
      rw [derivative_polynomial,derivative_of_natDegree_zero hdegree]
    have hempty := squarefree_original_real_roots_empty v hv hd
    have hcount : VariableRootBisection.realRootCount v q=0 := by
      simp only [VariableRootBisection.realRootCount,VariableRootBisection.realRootSet,
        hempty,Finset.filter_empty,Finset.card_empty]
    rw [rationalCount,doubledVariation_constant _ (squarefreeVector_ne_zero v hv) hdegree,
      doubledVariation_constant _ (squarefreeVector_ne_zero v hv) hdegree,hcount]
    norm_num
  · have hab : (VariableCauchyPoint.farLeft v q : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (VariableCauchyPoint.farLeft_lt v q).le
    have hvar := squarefreeGeneratedVariation_count_Ioc v hv hdegree
      (VariableCauchyPoint.farLeft v q : ℝ) (q : ℝ) hab
    rw [cauchy_root_filter v hv q] at hvar
    change generatedDoubledVariation (squarefreeVector v) (VariableCauchyPoint.farLeft v q : ℝ)-
      generatedDoubledVariation (squarefreeVector v) (q : ℝ) =
      2*(VariableRootBisection.realRootCount v q : ℤ) at hvar
    apply Rat.cast_injective (α := ℝ)
    unfold rationalCount
    push_cast
    rw [doubledVariation_real,doubledVariation_real]
    have hreal : (generatedDoubledVariation (squarefreeVector v)
        (VariableCauchyPoint.farLeft v q : ℝ) : ℝ)-
        (generatedDoubledVariation (squarefreeVector v) (q : ℝ) : ℝ) =
        2*(VariableRootBisection.realRootCount v q : ℝ) := by exact_mod_cast hvar
    linarith

theorem count_correct {n : ℕ} (v : Fin n → ℚ) (q : ℚ) :
    count v q=VariableRootBisection.realRootCount v q := by
  by_cases hv : v=0
  · subst v
    simp [count,VariableRootBisection.realRootCount,VariableRootBisection.realRootSet,polynomial_zero]
  · rw [count,ite_eq_right hv,rationalCount_correct v hv q,RationalNaturalOutput.natural_correct]

def realRootCountComputes (n : ℕ) :
    Computes (inputEncoding n) encodingNatBool
      (fun p => VariableRootBisection.realRootCount p.1 p.2) :=
  congrComputes (countComputes n) (fun p => count_correct p.1 p.2)

end
end Paper2.ExactInput.FixedRootCodec.SturmCounter
