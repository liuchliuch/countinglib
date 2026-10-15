import Paper2.ExactInput.FixedRootCodec.EuclideanPolynomial
import Mathlib.Analysis.Polynomial.CauchyBound

/-! A runtime rational Cauchy radius in a fixed coefficient dimension.
The leading nonzero slot is selected by a finite scan. Rational absolute values,
addition and division compute a strict bound, and an arbitrary rational query
point is shifted below that query and below every real root. -/
namespace Paper2.ExactInput.FixedRootCodec.VariableCauchyPoint
open Computability Paper2.Algebraic Paper2.Complexity Polynomial
open BinaryCompose FixedFieldMachines BellMachines VariablePolynomial
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def absoluteComputes : Computes rationalEncoding rationalEncoding (fun q : ℚ => |q|) :=
  congrComputes (ifComputes rationalNegativeComputes
    (rationalProvider.mulComputes (constantComputes _ rationalEncoding (-1)) (identityComputes _))
    (identityComputes _)) (fun q => by
      by_cases h : q < 0
      · simp [h,abs_of_neg h]
      · simp [h,abs_of_nonneg (le_of_not_gt h)])

def chooseLeading {n : ℕ} : List (Fin n) → (Fin n → ℚ) → ℚ
  | [],_ => 0
  | j::js,v => if v j = 0 then chooseLeading js v else v j

def chooseLeadingComputes {n : ℕ} : (js : List (Fin n)) →
    Computes (vectorEncoding n) rationalEncoding (chooseLeading js)
  | [] => constantComputes _ _ 0
  | j::js => congrComputes (ifComputes
      ((coordinateComputes n j).andThen (FixedRootCodec.zeroComputes rationalEncoding))
      (chooseLeadingComputes js) (coordinateComputes n j))
      (fun v => by simp only [chooseLeading,Function.comp_apply,decide_eq_true_eq])

def leading {n : ℕ} (v : Fin n → ℚ) : ℚ :=
  chooseLeading (List.finRange n).reverse v

def leadingComputes (n : ℕ) : Computes (vectorEncoding n) rationalEncoding (leading (n := n)) :=
  chooseLeadingComputes (List.finRange n).reverse

def coefficientSum {n : ℕ} (v : Fin n → ℚ) : ℚ := ∑ i : Fin n,|v i|

def coefficientSumComputes (n : ℕ) :
    Computes (vectorEncoding n) rationalEncoding (coefficientSum (n := n)) :=
  rationalProvider.sumComputes _ n _ (fun i => (coordinateComputes n i).andThen absoluteComputes)

def radius {n : ℕ} (v : Fin n → ℚ) : ℚ := 2+coefficientSum v/|leading v|

def radiusComputes (n : ℕ) : Computes (vectorEncoding n) rationalEncoding (radius (n := n)) :=
  rationalProvider.addComputes (constantComputes _ rationalEncoding 2)
    ((pairComputes (coefficientSumComputes n)
      ((leadingComputes n).andThen absoluteComputes)).andThen divisionComputes)

def farLeft {n : ℕ} (v : Fin n → ℚ) (q : ℚ) : ℚ := -(radius v+|q|+1)

def farLeftComputes (n : ℕ) :
    Computes (VariablePolynomial.inputEncoding n) rationalEncoding
      (fun p => farLeft p.1 p.2) := by
  let rad := (Wiring.firstComputes (vectorEncoding n) rationalEncoding).andThen (radiusComputes n)
  let point := (Wiring.secondComputes (vectorEncoding n) rationalEncoding).andThen absoluteComputes
  exact congrComputes (rationalProvider.mulComputes
    (constantComputes _ rationalEncoding (-1))
    (rationalProvider.addComputes (rationalProvider.addComputes rad point)
      (constantComputes _ rationalEncoding 1))) (fun p => by simp [farLeft])

theorem leading_at {n : ℕ} (j : Fin n) (v : Fin n → ℚ)
    (hj : v j ≠ 0) (hq : ∀ k : Fin n,j.val < k.val → v k = 0) :
    (polynomial v).leadingCoeff = v j := by
  have hd := polynomial_degree_eq j v hj hq
  rw [Polynomial.leadingCoeff,natDegree_eq_of_degree_eq_some hd,coefficient_eq]
  simp [j.isLt]

theorem chooseLeading_correct {n : ℕ} (js : List (Fin n)) (v : Fin n → ℚ)
    (horder : js.Pairwise (fun i j => j.val < i.val))
    (hzero : ∀ k : Fin n,k∉js → v k = 0) : chooseLeading js v = (polynomial v).leadingCoeff := by
  induction js with
  | nil =>
    have hv : v = 0 := funext (fun k => hzero k (by simp))
    simp [chooseLeading,hv,polynomial]
  | cons j js ih =>
    have hord := List.pairwise_cons.mp horder
    by_cases hj : v j = 0
    · rw [chooseLeading,ite_eq_left hj]
      apply ih hord.2
      intro k hk
      by_cases he : k = j
      · simpa [he] using hj
      · exact hzero k (by simp [he,hk])
    · rw [chooseLeading,ite_eq_right hj]
      apply (leading_at j v hj ?_).symm
      intro k hk
      apply hzero k
      simp only [List.mem_cons]
      rintro (he | hm)
      · subst k; omega
      · have hl := hord.1 k hm
        omega

theorem leading_correct {n : ℕ} (v : Fin n → ℚ) : leading v = (polynomial v).leadingCoeff := by
  apply chooseLeading_correct
  · rw [List.pairwise_reverse]
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa using hij
  · intro k hk
    exact False.elim (hk (by simp))

theorem coefficientSum_nonnegative {n : ℕ} (v : Fin n → ℚ) : 0 ≤ coefficientSum v :=
  Finset.sum_nonneg (fun i _ => abs_nonneg (v i))

theorem radius_ge_two {n : ℕ} (v : Fin n → ℚ) : 2 ≤ radius v := by
  have h : 0 ≤ coefficientSum v/|leading v| := div_nonneg (coefficientSum_nonnegative v) (abs_nonneg _)
  unfold radius
  linarith

theorem farLeft_lt {n : ℕ} (v : Fin n → ℚ) (q : ℚ) : farLeft v q < q := by
  have hr := radius_ge_two v
  have hq := neg_abs_le q
  unfold farLeft
  linarith

theorem coefficient_norm_le {n : ℕ} (v : Fin n → ℚ) (j : ℕ) :
    ‖((polynomial v).map (Rat.castHom ℂ)).coeff j‖≤(coefficientSum v : ℝ) := by
  rw [Polynomial.coeff_map,coefficient_eq]
  by_cases hj : j < n
  · simp only [hj,dite_true]
    change ‖(v ⟨j,hj⟩ : ℂ)‖≤(coefficientSum v : ℝ)
    rw [Complex.norm_ratCast,← Rat.cast_abs]
    exact_mod_cast Finset.single_le_sum (fun i _ => abs_nonneg (v i))
      (Finset.mem_univ (⟨j,hj⟩ : Fin n))
  · simp only [hj,dite_false,map_zero,norm_zero]
    exact_mod_cast coefficientSum_nonnegative v

theorem cauchyBound_le_radius {n : ℕ} (v : Fin n → ℚ) :
    (((polynomial v).map (Rat.castHom ℂ)).cauchyBound : ℝ)≤(radius v : ℝ) := by
  let P := (polynomial v).map (Rat.castHom ℂ)
  let S : NNReal := ⟨(coefficientSum v : ℝ),by exact_mod_cast coefficientSum_nonnegative v⟩
  have hs : (Finset.range P.natDegree).sup (fun j => ‖P.coeff j‖₊)≤S :=
    Finset.sup_le (fun j _ => coefficient_norm_le v j)
  have hb : P.cauchyBound ≤ S/‖P.leadingCoeff‖₊+1 := by
    unfold Polynomial.cauchyBound
    gcongr
  have hr : (P.cauchyBound : ℝ)≤(coefficientSum v : ℝ)/|(leading v : ℝ)|+1 := by
    have hc : ‖P.leadingCoeff‖=|(leading v : ℝ)| := by
      rw [Polynomial.leadingCoeff_map_of_injective (Rat.castHom ℂ).injective]
      change ‖((polynomial v).leadingCoeff : ℂ)‖=|(leading v : ℝ)|
      rw [Complex.norm_ratCast,← leading_correct]
    have hbr : (P.cauchyBound : ℝ)≤(S : ℝ)/‖P.leadingCoeff‖+1 := by
      exact_mod_cast hb
    rw [hc] at hbr
    exact hbr
  have he : (radius v : ℝ)=2+(coefficientSum v : ℝ)/|(leading v : ℝ)| := by
    unfold radius
    push_cast
    rfl
  rw [he]
  linarith

theorem complex_root_norm_lt {n : ℕ} (v : Fin n → ℚ) (hp : polynomial v ≠ 0)
    (z : ℂ) (hz : (polynomial v).aeval z = 0) : ‖z‖<(radius v : ℝ) := by
  have hr : ((polynomial v).map (Rat.castHom ℂ)).IsRoot z := by
    rw [Polynomial.IsRoot,Polynomial.eval_map]
    exact hz
  have hb : ‖z‖<(((polynomial v).map (Rat.castHom ℂ)).cauchyBound : ℝ) := by
    exact_mod_cast hr.norm_lt_cauchyBound (Polynomial.map_ne_zero hp)
  exact hb.trans_le (cauchyBound_le_radius v)

theorem real_root_abs_lt {n : ℕ} (v : Fin n → ℚ) (hp : polynomial v ≠ 0)
    (x : ℝ) (hx : (polynomial v).aeval x = 0) : |x|<(radius v : ℝ) := by
  have hc : (polynomial v).aeval (x : ℂ)=0 := by
    change (polynomial v).aeval (IsScalarTower.toAlgHom ℚ ℝ ℂ x)=0
    rw [Polynomial.aeval_algHom_apply,hx,map_zero]
  simpa only [Complex.norm_real,Real.norm_eq_abs] using complex_root_norm_lt v hp (x : ℂ) hc

theorem farLeft_lt_realRoot {n : ℕ} (v : Fin n → ℚ) (q : ℚ) (hp : polynomial v ≠ 0)
    (x : ℝ) (hx : (polynomial v).aeval x = 0) : (farLeft v q : ℝ)<x := by
  have hx' := (abs_lt.mp (real_root_abs_lt v hp x hx)).1
  have hq := abs_nonneg (q : ℝ)
  unfold farLeft
  push_cast
  linarith

theorem farLeft_not_realRoot {n : ℕ} (v : Fin n → ℚ) (q : ℚ) (hp : polynomial v ≠ 0) :
    (polynomial v).aeval (farLeft v q : ℝ)≠0 := by
  intro h
  exact lt_irrefl _ (farLeft_lt_realRoot v q hp _ h)

end
end Paper2.ExactInput.FixedRootCodec.VariableCauchyPoint
