import Paper2.ExactInput.FixedRootCodec.EuclideanPolynomial

/-! Actual rational coefficient quotient computation in a fixed vector size.
The cancellation circuit records each cancelling monomial in a quotient vector.
The descending loop and leading-slot selection are program constants; both
polynomial inputs remain runtime vectors. The zero divisor returns zero. -/
namespace Paper2.ExactInput.FixedRootCodec.VariablePolynomial
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines Polynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev QuotientState (n : ℕ) := Pair n × (Fin n → ℚ)
def quotientStateEncoding (n : ℕ) := pairEncoding (pairVectorEncoding n) (vectorEncoding n)

def quotientCancel {n : ℕ} (j i : Fin n) (p : QuotientState n) : QuotientState n :=
  (cancel j i p.1,fun k => p.2 k + if k.val = i.val-j.val then p.1.1 i/p.1.2 j else 0)

def quotientCancelComputes {n : ℕ} (j i : Fin n) :
    Computes (quotientStateEncoding n) (quotientStateEncoding n) (quotientCancel j i) := by
  let old := Wiring.firstComputes (pairVectorEncoding n) (vectorEncoding n)
  let current := Wiring.secondComputes (pairVectorEncoding n) (vectorEncoding n)
  let factor := (pairComputes (old.andThen (leftCoefficientComputes n i))
    (old.andThen (rightCoefficientComputes n j))).andThen divisionComputes
  let acc : Computes (quotientStateEncoding n) (vectorEncoding n)
      (fun p => (quotientCancel j i p).2) := by
    apply assembleComputes
    intro k
    by_cases hk : k.val = i.val-j.val
    · exact congrComputes (rationalProvider.addComputes
        (current.andThen (coordinateComputes n k)) factor)
        (fun p => by simp [quotientCancel,hk])
    · exact congrComputes (current.andThen (coordinateComputes n k))
        (fun p => by simp [quotientCancel,hk])
  exact pairComputes (old.andThen (cancelComputes j i)) acc

def quotientDown {n : ℕ} (j : Fin n) : ℕ → QuotientState n → QuotientState n
  | 0,p => p
  | t+1,p => if ht : t < n then
      if j.val ≤ t then quotientDown j t (quotientCancel j ⟨t,ht⟩ p) else quotientDown j t p
    else quotientDown j t p

def quotientDownComputes {n : ℕ} (j : Fin n) : (t : ℕ) →
    Computes (quotientStateEncoding n) (quotientStateEncoding n) (quotientDown j t)
  | 0 => identityComputes _
  | t+1 => by
    by_cases ht : t < n
    · by_cases hj : j.val ≤ t
      · exact congrComputes ((quotientCancelComputes j ⟨t,ht⟩).andThen (quotientDownComputes j t))
          (fun p => by simp [quotientDown,ht,hj])
      · exact congrComputes (quotientDownComputes j t) (fun p => by simp [quotientDown,ht,hj])
    · exact congrComputes (quotientDownComputes j t) (fun p => by simp [quotientDown,ht])

def quotientAt {n : ℕ} (j : Fin n) (p : Pair n) : Fin n → ℚ :=
  (quotientDown j n (p,0)).2

def quotientAtComputes {n : ℕ} (j : Fin n) :
    Computes (pairVectorEncoding n) (vectorEncoding n) (quotientAt j) :=
  congrComputes ((pairComputes (identityComputes (pairVectorEncoding n))
    (constantComputes (pairVectorEncoding n) (vectorEncoding n) 0)).andThen
      ((quotientDownComputes j n).andThen (Wiring.secondComputes _ _))) (fun _ => rfl)

def chooseQuotient {n : ℕ} : List (Fin n) → Pair n → Fin n → ℚ
  | [],_ => 0
  | j::js,p => if p.2 j = 0 then chooseQuotient js p else quotientAt j p

def chooseQuotientComputes {n : ℕ} : (js : List (Fin n)) →
    Computes (pairVectorEncoding n) (vectorEncoding n) (chooseQuotient js)
  | [] => constantComputes _ _ 0
  | j::js => congrComputes (ifComputes
      ((rightCoefficientComputes n j).andThen (FixedRootCodec.zeroComputes rationalEncoding))
      (chooseQuotientComputes js) (quotientAtComputes j))
      (fun p => by simp only [chooseQuotient,Function.comp_apply,decide_eq_true_eq])

def quotient {n : ℕ} (p : Pair n) : Fin n → ℚ :=
  chooseQuotient (List.finRange n).reverse p

def quotientComputes (n : ℕ) :
    Computes (pairVectorEncoding n) (vectorEncoding n) (quotient (n := n)) :=
  chooseQuotientComputes (List.finRange n).reverse

theorem polynomial_add {n : ℕ} (v w : Fin n → ℚ) :
    polynomial (v+w)=polynomial v+polynomial w := by
  ext k
  rw [coefficient_eq,coeff_add,coefficient_eq,coefficient_eq]
  by_cases hk : k < n <;> simp [hk]

theorem polynomial_zero {n : ℕ} : polynomial (0 : Fin n → ℚ)=0 := by
  simp [polynomial]

theorem polynomial_single {n : ℕ} (t : ℕ) (ht : t < n) (a : ℚ) :
    polynomial (fun k : Fin n => if k.val = t then a else 0)=monomial t a := by
  classical
  rw [polynomial,Finset.sum_eq_single (⟨t,ht⟩ : Fin n)]
  · simp
  · intro i _ hi
    have he : i.val ≠ t := fun h => hi (Fin.ext h)
    simp [he]
  · simp

@[simp] theorem quotientDown_first {n : ℕ} (j : Fin n) (t : ℕ) (p : QuotientState n) :
    (quotientDown j t p).1 = cancelDown j t p.1 := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
    simp only [quotientDown,cancelDown]
    split_ifs <;> simp only [ih,quotientCancel]

theorem quotientCancel_invariant {n : ℕ} (j i : Fin n) (hi : j.val ≤ i.val)
    (p : QuotientState n) (hq : ∀ k : Fin n,j.val < k.val → p.1.2 k = 0) :
    polynomial (quotientCancel j i p).1.1 +
      polynomial (quotientCancel j i p).2 * polynomial p.1.2 =
      polynomial p.1.1 + polynomial p.2 * polynomial p.1.2 := by
  simp only [quotientCancel]
  rw [cancel_polynomial j i hi p.1 hq]
  have ha : (fun k : Fin n => p.2 k + if k.val = i.val-j.val then p.1.1 i/p.1.2 j else 0) =
      p.2 + (fun k : Fin n => if k.val = i.val-j.val then p.1.1 i/p.1.2 j else 0) := rfl
  rw [ha,polynomial_add,polynomial_single _ (by omega)]
  ring

theorem quotientDown_invariant {n : ℕ} (j : Fin n) (t : ℕ) (p : QuotientState n)
    (hq : ∀ k : Fin n,j.val < k.val → p.1.2 k = 0) :
    polynomial (quotientDown j t p).1.1 +
      polynomial (quotientDown j t p).2 * polynomial p.1.2 =
      polynomial p.1.1 + polynomial p.2 * polynomial p.1.2 := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t < n
    · by_cases hj : j.val ≤ t
      · rw [quotientDown,dite_eq_left ht,ite_eq_left hj]
        exact (ih (quotientCancel j ⟨t,ht⟩ p) hq).trans
          (quotientCancel_invariant j ⟨t,ht⟩ hj p hq)
      · simpa only [quotientDown,ht,dite_true,hj,ite_false] using ih p hq
    · simpa only [quotientDown,ht,dite_false] using ih p hq

theorem quotientAt_identity {n : ℕ} (j : Fin n) (p : Pair n)
    (hq : ∀ k : Fin n,j.val < k.val → p.2 k = 0) :
    polynomial (remainderAt j p) + polynomial (quotientAt j p) * polynomial p.2 =
      polynomial p.1 := by
  have hi := quotientDown_invariant j n (p,0) hq
  rw [quotientDown_first,polynomial_zero,zero_mul,add_zero] at hi
  exact hi

theorem quotientAt_polynomial {n : ℕ} (j : Fin n) (p : Pair n)
    (hj : p.2 j ≠ 0) (hq : ∀ k : Fin n,j.val < k.val → p.2 k = 0) :
    polynomial (quotientAt j p)=polynomial p.1 / polynomial p.2 := by
  have hq0 : polynomial p.2 ≠ 0 := by
    intro hz
    have he := congrArg (fun P : ℚ[X] => P.coeff j.val) hz
    simp only [coefficient_eq,j.isLt,dite_true,Fin.eta,coeff_zero] at he
    exact hj he
  apply mul_right_cancel₀ hq0
  apply add_left_cancel (a := polynomial p.1 % polynomial p.2)
  rw [← remainderAt_polynomial j p hj hq,quotientAt_identity j p hq,
    remainderAt_polynomial j p hj hq]
  exact (EuclideanDomain.mod_add_div' (polynomial p.1) (polynomial p.2)).symm

theorem chooseQuotient_polynomial {n : ℕ} (js : List (Fin n)) (p : Pair n)
    (horder : js.Pairwise (fun i j => j.val < i.val))
    (hzero : ∀ k : Fin n,k∉js → p.2 k = 0) :
    polynomial (chooseQuotient js p)=polynomial p.1 / polynomial p.2 := by
  induction js with
  | nil =>
    have hq : p.2 = 0 := funext (fun k => hzero k (by simp))
    rw [chooseQuotient,hq,polynomial_zero]
    simp
  | cons j js ih =>
    have hord := List.pairwise_cons.mp horder
    by_cases hj : p.2 j = 0
    · rw [chooseQuotient,ite_eq_left hj]
      apply ih hord.2
      intro k hk
      by_cases he : k = j
      · simpa [he] using hj
      · exact hzero k (by simp [he,hk])
    · rw [chooseQuotient,ite_eq_right hj]
      apply quotientAt_polynomial j p hj
      intro k hk
      apply hzero k
      simp only [List.mem_cons]
      rintro (he | hm)
      · subst k; omega
      · have hl := hord.1 k hm
        omega

theorem quotient_polynomial {n : ℕ} (p : Pair n) :
    polynomial (quotient p)=polynomial p.1 / polynomial p.2 := by
  apply chooseQuotient_polynomial
  · rw [List.pairwise_reverse]
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa using hij
  · intro k hk
    exact False.elim (hk (by simp))

end
end Paper2.ExactInput.FixedRootCodec.VariablePolynomial
