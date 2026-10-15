import Paper2.ExactInput.FixedRootCodec.VariablePolynomial

/-! Fixed-degree polynomial cancellation. The divisor and dividend remain
runtime coefficient vectors. A finite descending list of slots compiles to
actual rational reciprocal, multiplication, addition and selection programs.
The zero divisor has the usual total remainder convention. -/
namespace Paper2.ExactInput.FixedRootCodec.VariablePolynomial
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines Polynomial
noncomputable section

abbrev Pair (n : ℕ) := (Fin n → ℚ) × (Fin n → ℚ)
def pairVectorEncoding (n : ℕ) := pairEncoding (vectorEncoding n) (vectorEncoding n)

def leftCoefficientComputes (n : ℕ) (i : Fin n) :
    Computes (pairVectorEncoding n) rationalEncoding (fun p => p.1 i) :=
  congrComputes ((Wiring.firstComputes _ _).andThen (coordinateComputes n i)) (fun _ => rfl)

def rightCoefficientComputes (n : ℕ) (i : Fin n) :
    Computes (pairVectorEncoding n) rationalEncoding (fun p => p.2 i) :=
  congrComputes ((Wiring.secondComputes _ _).andThen (coordinateComputes n i)) (fun _ => rfl)

def shifted {n : ℕ} (shift : ℕ) (q : Fin n → ℚ) (k : Fin n) : ℚ :=
  if h : shift ≤ k.val then q ⟨k.val-shift,by omega⟩ else 0

def cancel {n : ℕ} (j i : Fin n) (p : Pair n) : Pair n :=
  (fun k => p.1 k - (p.1 i / p.2 j) * shifted (i.val-j.val) p.2 k,p.2)

def cancelComputes {n : ℕ} (j i : Fin n) :
    Computes (pairVectorEncoding n) (pairVectorEncoding n) (cancel j i) := by
  let factor := (pairComputes (leftCoefficientComputes n i)
    (rightCoefficientComputes n j)).andThen divisionComputes
  let value (k : Fin n) : Computes (pairVectorEncoding n) rationalEncoding
      (fun p => shifted (i.val-j.val) p.2 k) := by
    by_cases h : i.val-j.val ≤ k.val
    · exact congrComputes (rightCoefficientComputes n ⟨k.val-(i.val-j.val),by omega⟩)
        (fun p => by simp [shifted,h])
    · exact congrComputes (constantComputes (pairVectorEncoding n) rationalEncoding 0)
        (fun p => by simp [shifted,h])
  let first : Computes (pairVectorEncoding n) (vectorEncoding n) (fun p => (cancel j i p).1) :=
    assembleComputes _ n _ (fun k => congrComputes
      (rationalProvider.addComputes (leftCoefficientComputes n k)
        (rationalProvider.mulComputes
          (constantComputes _ rationalEncoding (-1))
          (rationalProvider.mulComputes factor (value k))))
      (fun p => by
        dsimp [cancel]
        ring))
  exact pairComputes first (Wiring.secondComputes _ _)

def cancelDown {n : ℕ} (j : Fin n) : ℕ → Pair n → Pair n
  | 0,p => p
  | r+1,p => if h : r<n then
      if j.val ≤ r then cancelDown j r (cancel j ⟨r,h⟩ p) else cancelDown j r p
    else cancelDown j r p

def cancelDownComputes {n : ℕ} (j : Fin n) : (r : ℕ) →
    Computes (pairVectorEncoding n) (pairVectorEncoding n) (cancelDown j r)
  | 0 => identityComputes _
  | r+1 => by
    by_cases h : r<n
    · by_cases hj : j.val≤r
      · exact congrComputes ((cancelComputes j ⟨r,h⟩).andThen (cancelDownComputes j r))
          (fun p => by simp [cancelDown,h,hj])
      · exact congrComputes (cancelDownComputes j r) (fun p => by simp [cancelDown,h,hj])
    · exact congrComputes (cancelDownComputes j r) (fun p => by simp [cancelDown,h])

def remainderAt {n : ℕ} (j : Fin n) (p : Pair n) : Fin n → ℚ :=
  (cancelDown j n p).1

def remainderAtComputes {n : ℕ} (j : Fin n) :
    Computes (pairVectorEncoding n) (vectorEncoding n) (remainderAt j) :=
  congrComputes ((cancelDownComputes j n).andThen
    (Wiring.firstComputes _ _)) (fun _ => rfl)

def chooseRemainder {n : ℕ} : List (Fin n) → Pair n → Fin n → ℚ
  | [],p => p.1
  | j::js,p => if p.2 j = 0 then chooseRemainder js p else remainderAt j p

def chooseRemainderComputes {n : ℕ} : (js : List (Fin n)) →
    Computes (pairVectorEncoding n) (vectorEncoding n) (chooseRemainder js)
  | [] => Wiring.firstComputes _ _
  | j::js => congrComputes (ifComputes
      ((rightCoefficientComputes n j).andThen (FixedRootCodec.zeroComputes rationalEncoding))
      (chooseRemainderComputes js) (remainderAtComputes j))
      (fun p => by simp only [chooseRemainder,Function.comp_apply,decide_eq_true_eq])

def remainder {n : ℕ} (p : Pair n) : Fin n → ℚ :=
  chooseRemainder (List.finRange n).reverse p

def remainderComputes (n : ℕ) :
    Computes (pairVectorEncoding n) (vectorEncoding n) (remainder (n := n)) :=
  chooseRemainderComputes (List.finRange n).reverse

theorem monomial_mul_coefficient (q : ℚ[X]) (s k : ℕ) (a : ℚ) :
    (monomial s a * q).coeff k =
      if s ≤ k then a * q.coeff (k-s) else 0 := by
  rw [← C_mul_X_pow_eq_monomial,mul_assoc,coeff_C_mul,coeff_X_pow_mul']
  split_ifs <;> simp

theorem cancel_polynomial {n : ℕ} (j i : Fin n) (hi : j.val ≤ i.val)
    (p : Pair n) (hq : ∀ k : Fin n, j.val < k.val → p.2 k = 0) :
    polynomial (cancel j i p).1 = polynomial p.1 -
      monomial (i.val-j.val) (p.1 i / p.2 j) * polynomial p.2 := by
  ext k
  rw [coefficient_eq,coeff_sub,coefficient_eq,monomial_mul_coefficient,coefficient_eq]
  by_cases hk : k < n
  · simp only [hk,dite_true]
    dsimp [cancel,shifted]
    by_cases hs : i.val-j.val ≤ k
    · have hkn : k-(i.val-j.val)<n := by omega
      simp [hs,hkn]
    · simp [hs]
  · have hkn : ¬ k-(i.val-j.val)<n ∨
        j.val < k-(i.val-j.val) := by omega
    simp only [hk,dite_false,zero_sub]
    by_cases hs : i.val-j.val ≤ k
    · simp only [hs,ite_true]
      by_cases ht : k-(i.val-j.val)<n
      · have he : p.2 (⟨k-(i.val-j.val),ht⟩ : Fin n) = 0 :=
          hq _ (by change j.val < k-(i.val-j.val); omega)
        simp [ht,he]
      · simp [ht]
    · simp [hs]

theorem cancel_coefficient {n : ℕ} (j i : Fin n) (hi : j.val ≤ i.val)
    (p : Pair n) (hj : p.2 j ≠ 0) : (cancel j i p).1 i = 0 := by
  have hshift : i.val-j.val ≤ i.val := Nat.sub_le _ _
  have he : i.val-(i.val-j.val) = j.val := by omega
  simp only [cancel,shifted,hshift,dite_true]
  have hfin : (⟨i.val-(i.val-j.val),by omega⟩ : Fin n) = j := Fin.ext he
  rw [hfin,div_mul_cancel₀ _ hj,sub_self]

theorem cancel_preserves_above {n : ℕ} (j i k : Fin n)
    (hi : j.val ≤ i.val) (hik : i.val < k.val) (p : Pair n)
    (hq : ∀ l : Fin n, j.val < l.val → p.2 l = 0) :
    (cancel j i p).1 k = p.1 k := by
  have hs : i.val-j.val ≤ k.val := by omega
  simp only [cancel,shifted,hs,dite_true]
  have he : p.2 (⟨k.val-(i.val-j.val),by omega⟩ : Fin n) = 0 :=
    hq _ (by change j.val < k.val-(i.val-j.val); omega)
  rw [he,mul_zero,sub_zero]

@[simp] theorem cancelDown_second {n : ℕ} (j : Fin n) (r : ℕ) (p : Pair n) :
    (cancelDown j r p).2 = p.2 := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    simp only [cancelDown]
    split_ifs <;> simp only [ih,cancel]

theorem cancelDown_annihilates {n : ℕ} (j : Fin n) (r : ℕ) (hr : r ≤ n)
    (p : Pair n) (hj : p.2 j ≠ 0)
    (hq : ∀ k : Fin n, j.val < k.val → p.2 k = 0)
    (hp : ∀ k : Fin n, r ≤ k.val → j.val ≤ k.val → p.1 k = 0) :
    ∀ k : Fin n, j.val ≤ k.val → (cancelDown j r p).1 k = 0 := by
  induction r generalizing p with
  | zero => exact fun k hk => hp k (Nat.zero_le _) hk
  | succ r ih =>
    have hri : r<n := by omega
    by_cases hjr : j.val≤r
    · rw [cancelDown,dite_eq_left hri,ite_eq_left hjr]
      apply ih (by omega) (cancel j ⟨r,hri⟩ p) hj hq
      intro k hrk hjk
      by_cases he : k.val=r
      · have hek : k = (⟨r,hri⟩ : Fin n) := Fin.ext he
        subst k
        exact cancel_coefficient j ⟨r,hri⟩ hjr p hj
      · rw [cancel_preserves_above j ⟨r,hri⟩ k hjr (by change r<k.val; omega) p hq]
        exact hp k (by omega) hjk
    · rw [cancelDown,dite_eq_left hri,ite_eq_right hjr]
      apply ih (by omega) p hj hq
      exact fun k _ hjk => hp k (by omega) hjk

theorem cancelDown_mod {n : ℕ} (j : Fin n) (r : ℕ) (p : Pair n)
    (hq : ∀ k : Fin n, j.val < k.val → p.2 k = 0) :
    polynomial (cancelDown j r p).1 % polynomial p.2 =
      polynomial p.1 % polynomial p.2 := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    by_cases hr : r<n
    · by_cases hj : j.val≤r
      · rw [cancelDown,dite_eq_left hr,ite_eq_left hj]
        change _ % polynomial (cancel j ⟨r,hr⟩ p).2 = _
        rw [ih (cancel j ⟨r,hr⟩ p) hq]
        change polynomial (cancel j ⟨r,hr⟩ p).1 % polynomial p.2 = _
        apply Polynomial.mod_eq_of_dvd_sub
        rw [cancel_polynomial j ⟨r,hr⟩ hj p hq]
        exact ⟨-monomial (r-j.val) (p.1 ⟨r,hr⟩ / p.2 j),by ring⟩
      · simpa only [cancelDown,hr,dite_true,hj,ite_false] using ih p hq
    · simpa only [cancelDown,hr,dite_false] using ih p hq

theorem polynomial_degree_eq {n : ℕ} (j : Fin n) (q : Fin n → ℚ)
    (hj : q j ≠ 0) (hq : ∀ k : Fin n, j.val < k.val → q k = 0) :
    (polynomial q).degree = j.val := by
  apply le_antisymm
  · apply (degree_le_iff_coeff_zero _ _).mpr
    intro k hk
    rw [coefficient_eq]
    by_cases hn : k<n
    · simp only [hn,dite_true]
      apply hq
      change j.val < k
      exact_mod_cast hk
    · simp [hn]
  · apply le_degree_of_ne_zero
    simpa only [coefficient_eq,j.isLt,dite_true,Fin.eta] using hj

theorem remainderAt_polynomial {n : ℕ} (j : Fin n) (p : Pair n)
    (hj : p.2 j ≠ 0) (hq : ∀ k : Fin n, j.val < k.val → p.2 k = 0) :
    polynomial (remainderAt j p) = polynomial p.1 % polynomial p.2 := by
  have hq0 : polynomial p.2 ≠ 0 := by
    intro hz
    have hc := congrArg (fun q : ℚ[X] => q.coeff j.val) hz
    simp only [coefficient_eq,j.isLt,dite_true,coeff_zero,Fin.eta] at hc
    exact hj hc
  have hd := polynomial_degree_eq j p.2 hj hq
  have ha := cancelDown_annihilates j n le_rfl p hj hq
    (fun k hn _ => False.elim (Nat.not_le_of_lt k.isLt hn))
  have hr : (polynomial (remainderAt j p)).degree < (polynomial p.2).degree := by
    rw [hd]
    apply (degree_lt_iff_coeff_zero _ _).mpr
    intro k hk
    rw [coefficient_eq]
    by_cases hn : k<n
    · simp only [hn,dite_true]
      exact ha ⟨k,hn⟩ hk
    · simp [hn]
  have hm := cancelDown_mod j n p hq
  change polynomial (remainderAt j p) % polynomial p.2 = _ at hm
  rw [(mod_eq_self_iff hq0).mpr hr] at hm
  exact hm

theorem chooseRemainder_polynomial {n : ℕ} (js : List (Fin n)) (p : Pair n)
    (horder : js.Pairwise (fun i j => j.val < i.val))
    (hzero : ∀ k : Fin n, k ∉ js → p.2 k = 0) :
    polynomial (chooseRemainder js p) = polynomial p.1 % polynomial p.2 := by
  induction js with
  | nil =>
    have hq : p.2 = 0 := funext (fun k => hzero k (by simp))
    have hp : polynomial p.2 = 0 := by simp [hq,polynomial]
    simp [chooseRemainder,hp]
  | cons j js ih =>
    have hord := List.pairwise_cons.mp horder
    by_cases hj : p.2 j = 0
    · rw [chooseRemainder,ite_eq_left hj]
      apply ih hord.2
      intro k hk
      by_cases he : k=j
      · simpa [he] using hj
      · exact hzero k (by simp [he,hk])
    · rw [chooseRemainder,ite_eq_right hj]
      apply remainderAt_polynomial j p hj
      intro k hk
      apply hzero k
      simp only [List.mem_cons]
      rintro (he | hm)
      · subst k; omega
      · have hl := hord.1 k hm
        omega

theorem remainder_polynomial {n : ℕ} (p : Pair n) :
    polynomial (remainder p) = polynomial p.1 % polynomial p.2 := by
  apply chooseRemainder_polynomial
  · rw [List.pairwise_reverse]
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa using hij
  · intro k hk
    exact False.elim (hk (by simp))

end
end Paper2.ExactInput.FixedRootCodec.VariablePolynomial
