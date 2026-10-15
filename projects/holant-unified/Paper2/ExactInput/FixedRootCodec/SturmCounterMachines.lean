import Paper2.ExactInput.FixedRootCodec.GeneratedSturmChain
import Paper2.ExactInput.FixedRootCodec.VariableCauchyPoint
import Paper2.ExactInput.FixedRootCodec.RationalNaturalOutput

/-! A concrete distinct-real-root counter for varying rational coefficients.
The program computes a squarefree quotient, its bounded Euclidean stages,
and the doubled sign-variation difference at two actual rational points.
Only the vector capacity is fixed; the coefficients and query are input. -/
namespace Paper2.ExactInput.FixedRootCodec.SturmCounter
open Computability Paper2.Algebraic Paper2.Complexity Polynomial
open BinaryCompose FixedFieldMachines BellMachines VariablePolynomial
open scoped BigOperators
noncomputable section

def generatedSign {n : ℕ} (p : (Fin n → ℚ) × ℚ) (k : ℕ) : ℚ :=
  rationalSign (evaluation (generatedTerm p.1 k) p.2)

def generatedSignComputes (n k : ℕ) :
    Computes (inputEncoding n) rationalEncoding (fun p => generatedSign p k) :=
  congrComputes ((pairComputes
    ((Wiring.firstComputes _ _).andThen (generatedTermComputes n k))
    (Wiring.secondComputes _ _)).andThen
      ((evaluationComputes n).andThen rationalSignComputes)) (fun _ => rfl)

def doubledVariation {n : ℕ} (v : Fin n → ℚ) (q : ℚ) : ℚ :=
  (∑ i : Fin (n+1), (1-generatedSign (v,q) i.val*generatedSign (v,q) (i.val+1))) -
    if evaluation v q=0 then 1 else 0

def doubledVariationComputes (n : ℕ) :
    Computes (inputEncoding n) rationalEncoding (fun p => doubledVariation p.1 p.2) := by
  let summand (i : Fin (n+1)) := rationalProvider.addComputes
    (constantComputes (inputEncoding n) rationalEncoding 1)
    (rationalProvider.mulComputes (constantComputes _ rationalEncoding (-1))
      (rationalProvider.mulComputes (generatedSignComputes n i.val)
        (generatedSignComputes n (i.val+1))))
  let sum := rationalProvider.sumComputes (inputEncoding n) (n+1) _ summand
  let head := ifComputes (VariablePolynomial.zeroComputes n)
    (constantComputes _ rationalEncoding 1) (constantComputes _ rationalEncoding 0)
  exact congrComputes (rationalProvider.addComputes sum
    (rationalProvider.mulComputes (constantComputes _ rationalEncoding (-1)) head))
    (fun p => by
      simp only [decide_eq_true_eq]
      simp only [doubledVariation,neg_one_mul,sub_eq_add_neg])

theorem rationalSign_real (q : ℚ) :
    (rationalSign q : ℝ) = (SturmCount.integerSign (q : ℝ) : ℝ) := by
  rcases lt_trichotomy q 0 with h | h | h
  · have hr : (q : ℝ) < 0 := by exact_mod_cast h
    simp [rationalSign,ne_of_lt h,h,SturmCount.integerSign,sign_neg hr]
  · subst q
    simp [rationalSign]
  · have hr : 0 < (q : ℝ) := by exact_mod_cast h
    simp [rationalSign,ne_of_gt h,not_lt_of_ge h.le,SturmCount.integerSign,sign_pos hr]

theorem realEvaluation {n : ℕ} (v : Fin n → ℚ) (q : ℚ) :
    ((polynomial v).map (algebraMap ℚ ℝ)).eval (q : ℝ) = (evaluation v q : ℝ) := by
  rw [eval_map]
  change (polynomial v).eval₂ (algebraMap ℚ ℝ) ((algebraMap ℚ ℝ) q) =
    (algebraMap ℚ ℝ) (evaluation v q)
  rw [eval₂_hom,evaluation_eq]

theorem doubledVariation_real {n : ℕ} (v : Fin n → ℚ) (q : ℚ) :
    (doubledVariation v q : ℝ) = (generatedDoubledVariation v (q : ℝ) : ℝ) := by
  unfold doubledVariation generatedDoubledVariation
  push_cast
  rw [show (∑ i : Fin (n+1),
      (1-(generatedSign (v,q) i.val : ℝ)*(generatedSign (v,q) (i.val+1) : ℝ))) =
      ∑ i ∈ Finset.range (n+1),
        (1-(generatedSign (v,q) i : ℝ)*(generatedSign (v,q) (i+1) : ℝ)) from
      Fin.sum_univ_eq_sum_range (fun i =>
        (1-(generatedSign (v,q) i : ℝ)*(generatedSign (v,q) (i+1) : ℝ))) (n+1)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [generatedSign,rationalSign_real,realEvaluation]
  · rw [realEvaluation]
    have hz : (evaluation v q : ℝ)=0 ↔ evaluation v q=0 := Rat.cast_eq_zero
    simp only [hz]
    split_ifs <;> norm_num

def rationalCount {n : ℕ} (v : Fin n → ℚ) (q : ℚ) : ℚ :=
  (doubledVariation (squarefreeVector v) (VariableCauchyPoint.farLeft v q)-
    doubledVariation (squarefreeVector v) q)/2

def rationalCountComputes (n : ℕ) :
    Computes (inputEncoding n) rationalEncoding (fun p => rationalCount p.1 p.2) := by
  let squarefree := (Wiring.firstComputes (vectorEncoding n) rationalEncoding).andThen
    (squarefreeComputes n)
  let left := (pairComputes squarefree (VariableCauchyPoint.farLeftComputes n)).andThen
    (doubledVariationComputes n)
  let right := (pairComputes squarefree (Wiring.secondComputes _ _)).andThen
    (doubledVariationComputes n)
  exact congrComputes (rationalProvider.mulComputes
    (rationalProvider.addComputes left
      (rationalProvider.mulComputes (constantComputes _ rationalEncoding (-1)) right))
    (constantComputes _ rationalEncoding (2⁻¹)))
    (fun p => by simp only [rationalCount,neg_one_mul,sub_eq_add_neg,div_eq_mul_inv,
      Function.comp_apply])

def count {n : ℕ} (v : Fin n → ℚ) (q : ℚ) : ℕ :=
  if v=0 then 0 else RationalNaturalOutput.value (rationalCount v q)

def countComputes (n : ℕ) :
    Computes (inputEncoding n) encodingNatBool (fun p => count p.1 p.2) :=
  congrComputes (ifComputes
    ((Wiring.firstComputes _ _).andThen (FixedRootCodec.zeroComputes (vectorEncoding n)))
    (constantComputes _ encodingNatBool 0)
    ((rationalCountComputes n).andThen RationalNaturalOutput.computes))
    (fun p => by simp only [count,Function.comp_apply,decide_eq_true_eq])

end
end Paper2.ExactInput.FixedRootCodec.SturmCounter
