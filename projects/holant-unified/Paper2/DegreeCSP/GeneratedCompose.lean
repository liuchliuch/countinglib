import Paper2.DegreeCSP.OrderedPresentation
import Paper2.DegreeCSP.GeneratedRelabel

/-! Actual composition of finite degree-generated presentations. Hidden
variables remain disjoint in products; summation merely moves a boundary
variable into the hidden set and changes no occurrence. -/
namespace Paper2.DegreeCSP
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

namespace Presentation
variable {K B : Type}

theorem degree_eq_sum (P : Presentation K B) (v : B ⊕ Fin P.hiddenCount) :
    P.degree v = ∑ c, ∑ j, if P.scope c j=v then 1 else 0 := by
  rw [degree,Nat.card_eq_fintype_card,Fintype.card_subtype,
    Finset.card_filter,Fintype.sum_sigma]
  rfl

def leftScope {H J : Type} (p : B ⊕ H) : B ⊕ (H ⊕ J) := Sum.map id Sum.inl p
def rightScope {H J : Type} (p : B ⊕ J) : B ⊕ (H ⊕ J) := Sum.map id Sum.inr p

@[simp] theorem leftScope_boundary {H J : Type} (p : B ⊕ H) (b : B) :
    (leftScope (J:=J) p=Sum.inl b) ↔ p=Sum.inl b := by cases p <;> simp [leftScope]
@[simp] theorem rightScope_boundary {H J : Type} (p : B ⊕ J) (b : B) :
    (rightScope (H:=H) p=Sum.inl b) ↔ p=Sum.inl b := by cases p <;> simp [rightScope]
@[simp] theorem leftScope_left {H J : Type} (p : B ⊕ H) (h : H) :
    (leftScope (J:=J) p=Sum.inr (Sum.inl h)) ↔ p=Sum.inr h := by cases p <;> simp [leftScope]
@[simp] theorem rightScope_right {H J : Type} (p : B ⊕ J) (j : J) :
    (rightScope (H:=H) p=Sum.inr (Sum.inr j)) ↔ p=Sum.inr j := by cases p <;> simp [rightScope]
@[simp] theorem leftScope_not_right {H J : Type} (p : B ⊕ H) (j : J) :
    leftScope p≠Sum.inr (Sum.inr j) := by cases p <;> simp [leftScope]
@[simp] theorem rightScope_not_left {H J : Type} (p : B ⊕ J) (h : H) :
    rightScope p≠Sum.inr (Sum.inl h) := by cases p <;> simp [rightScope]

def productArity (P Q : Presentation K B) : Fin P.constraints ⊕ Fin Q.constraints → ℕ :=
  Sum.elim P.arity Q.arity

def productConstraint (P Q : Presentation K B) :
    (c : Fin P.constraints ⊕ Fin Q.constraints) → Signature K (productArity P Q c)
  | .inl c => P.constraint c
  | .inr c => Q.constraint c

def productScope (P Q : Presentation K B) :
    (c : Fin P.constraints ⊕ Fin Q.constraints) → Fin (productArity P Q c) →
      B ⊕ (Fin P.hiddenCount ⊕ Fin Q.hiddenCount)
  | .inl c,j => leftScope (P.scope c j)
  | .inr c,j => rightScope (Q.scope c j)

def disjointProduct (P Q : Presentation K B) : Presentation K B :=
  OrderedPresentation.ordered (productArity P Q) (productConstraint P Q) (productScope P Q)

theorem product_boundary_degree (P Q : Presentation K B) (b : B) :
    (P.disjointProduct Q).degree (Sum.inl b) = P.degree (Sum.inl b)+Q.degree (Sum.inl b) := by
  have h := OrderedPresentation.ordered_degree (productArity P Q) (productConstraint P Q)
    (productScope P Q) (Sum.inl b)
  simpa only [disjointProduct,OrderedPresentation.variableEquiv,Equiv.sumCongr_apply,
    Equiv.refl_apply,Sum.map_inl,Fintype.sum_sum_type,productArity,Sum.elim_inl,Sum.elim_inr,
    productScope,leftScope_boundary,rightScope_boundary,degree_eq_sum] using h

theorem product_hidden_left_degree (P Q : Presentation K B) (h : Fin P.hiddenCount) :
    (P.disjointProduct Q).degree (OrderedPresentation.variableEquiv
      (B:=B) (H:=Fin P.hiddenCount ⊕ Fin Q.hiddenCount) (Sum.inr (Sum.inl h))) =
      P.degree (Sum.inr h) := by
  have hd := OrderedPresentation.ordered_degree (productArity P Q) (productConstraint P Q)
    (productScope P Q) (Sum.inr (Sum.inl h))
  simpa only [disjointProduct,Fintype.sum_sum_type,productArity,Sum.elim_inl,Sum.elim_inr,
    productScope,leftScope_left,rightScope_not_left,ite_false,Finset.sum_const_zero,
    add_zero,degree_eq_sum] using hd

theorem product_hidden_right_degree (P Q : Presentation K B) (j : Fin Q.hiddenCount) :
    (P.disjointProduct Q).degree (OrderedPresentation.variableEquiv
      (B:=B) (H:=Fin P.hiddenCount ⊕ Fin Q.hiddenCount) (Sum.inr (Sum.inr j))) =
      Q.degree (Sum.inr j) := by
  have hd := OrderedPresentation.ordered_degree (productArity P Q) (productConstraint P Q)
    (productScope P Q) (Sum.inr (Sum.inr j))
  simpa only [disjointProduct,Fintype.sum_sum_type,productArity,Sum.elim_inl,Sum.elim_inr,
    productScope,rightScope_right,leftScope_not_right,ite_false,Finset.sum_const_zero,
    zero_add,degree_eq_sum] using hd

theorem product_divisible (P Q : Presentation K B) {k : ℕ}
    (hP : P.DegreeDivisible k) (hQ : Q.DegreeDivisible k) :
    (P.disjointProduct Q).DegreeDivisible k := by
  intro v
  obtain ⟨w,rfl⟩ := (OrderedPresentation.variableEquiv :
    B ⊕ (Fin P.hiddenCount ⊕ Fin Q.hiddenCount) ≃ _).surjective v
  rcases w with b | (h | j)
  · change k ∣ (P.disjointProduct Q).degree (Sum.inl b)
    rw [product_boundary_degree]
    exact Nat.dvd_add (hP _) (hQ _)
  · rw [product_hidden_left_degree]
    exact hP _
  · rw [product_hidden_right_degree]
    exact hQ _

theorem product_uses (P Q : Presentation K B) {F : SignatureFamily K}
    (hP : P.Uses F) (hQ : Q.Uses F) : (P.disjointProduct Q).Uses F := by
  apply OrderedPresentation.ordered_uses
  rintro (c | c)
  · exact hP c
  · exact hQ c

theorem product_value [CommSemiring K] (P Q : Presentation K B) (x : B → Bool) :
    (P.disjointProduct Q).value x = P.value x*Q.value x := by
  classical
  let _ : DecidableEq (Fin P.hiddenCount ⊕ Fin Q.hiddenCount) :=
    fun a b=>Classical.propDecidable (a=b)
  rw [disjointProduct,OrderedPresentation.ordered_value]
  let e := Equiv.sumArrowEquivProdArrow (Fin P.hiddenCount) (Fin Q.hiddenCount) Bool
  let w : ((Fin P.hiddenCount ⊕ Fin Q.hiddenCount) → Bool) → K := fun y =>
    ∏ c,productConstraint P Q c (fun i=>Sum.elim x y (productScope P Q c i))
  change (∑ y,w y) = _
  rw [← e.symm.sum_comp w,Fintype.sum_prod_type,value,value,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  dsimp only [w]
  rw [Fintype.prod_sum_type]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro c _
    congr 1
    funext i
    change Sum.elim x (e.symm (y,z)) (leftScope (P.scope c i)) = Sum.elim x y (P.scope c i)
    cases P.scope c i <;> rfl
  · apply Finset.prod_congr rfl
    intro c _
    congr 1
    funext i
    change Sum.elim x (e.symm (y,z)) (rightScope (Q.scope c i)) = Sum.elim x z (Q.scope c i)
    cases Q.scope c i <;> rfl

/-- The old last boundary position becomes the new last hidden position. -/
def moveLast (n h : ℕ) : (Fin (n+1) ⊕ Fin h) ≃ (Fin n ⊕ Fin (h+1)) where
  toFun
    | .inl i => Fin.lastCases (Sum.inr (Fin.last h)) (fun j=>Sum.inl j) i
    | .inr i => Sum.inr i.castSucc
  invFun
    | .inl i => Sum.inl i.castSucc
    | .inr i => Fin.lastCases (Sum.inl (Fin.last n)) (fun j=>Sum.inr j) i
  left_inv := by
    rintro (i | i)
    · refine Fin.lastCases ?_ (fun j=>?_) i <;> simp
    · simp
  right_inv := by
    rintro (i | i)
    · simp
    · refine Fin.lastCases ?_ (fun j=>?_) i <;> simp

def sumLast {n : ℕ} (P : Presentation K (Fin (n+1))) : Presentation K (Fin n) where
  hiddenCount := P.hiddenCount+1
  constraints := P.constraints
  arity := P.arity
  constraint := P.constraint
  scope c i := moveLast n P.hiddenCount (P.scope c i)

def sumLastFiber {n : ℕ} (P : Presentation K (Fin (n+1)))
    (v : Fin (n+1) ⊕ Fin P.hiddenCount) :
    P.sumLast.Fiber (moveLast n P.hiddenCount v) ≃ P.Fiber v where
  toFun p := ⟨p.val,(moveLast n P.hiddenCount).injective p.property⟩
  invFun p := ⟨p.val,congrArg (moveLast n P.hiddenCount) p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sumLast_degree {n : ℕ} (P : Presentation K (Fin (n+1)))
    (v : Fin (n+1) ⊕ Fin P.hiddenCount) :
    P.sumLast.degree (moveLast n P.hiddenCount v) = P.degree v :=
  Nat.card_congr (P.sumLastFiber v)

theorem sumLast_divisible {n : ℕ} (P : Presentation K (Fin (n+1))) {k : ℕ}
    (hP : P.DegreeDivisible k) : P.sumLast.DegreeDivisible k := by
  intro v
  obtain ⟨w,rfl⟩ := (moveLast n P.hiddenCount).surjective v
  rw [sumLast_degree]
  exact hP w

theorem sumLast_uses {n : ℕ} (P : Presentation K (Fin (n+1))) {F : SignatureFamily K}
    (hP : P.Uses F) : P.sumLast.Uses F := hP

theorem moveLast_assignment {n h : ℕ} (x : Fin n → Bool) (y : Fin h → Bool) (b : Bool)
    (v : Fin (n+1) ⊕ Fin h) :
    Sum.elim x (Fin.snoc y b) (moveLast n h v) = Sum.elim (Fin.snoc x b) y v := by
  cases v with
  | inl i => refine Fin.lastCases ?_ (fun j=>?_) i <;> simp [moveLast]
  | inr i => simp [moveLast]

theorem sumLast_value {n : ℕ} [CommSemiring K] (P : Presentation K (Fin (n+1)))
    (x : Fin n → Bool) : P.sumLast.value x = ∑ b : Bool,P.value (Fin.snoc x b) := by
  classical
  let e := Fin.snocEquiv (fun _ : Fin (P.hiddenCount+1)=>Bool)
  unfold value
  simp only [sumLast]
  rw [← e.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.prod_congr rfl
  intro c _
  congr 1
  funext i
  exact moveLast_assignment x y b (P.scope c i)

end Presentation

theorem generated_hadamard {K : Type} [CommSemiring K] {F : SignatureFamily K}
    {k n : ℕ} {f g : Signature K n} (hf : Generated F k f) (hg : Generated F k g) :
    Generated F k (fun x=>f x*g x) := by
  obtain ⟨P,hPF,hPk,hPf⟩ := hf
  obtain ⟨Q,hQF,hQk,hQg⟩ := hg
  refine ⟨P.disjointProduct Q,P.product_uses Q hPF hQF,P.product_divisible Q hPk hQk,?_⟩
  funext x
  rw [Presentation.product_value,hPf,hQg]

theorem generated_sum_last {K : Type} [CommSemiring K] {F : SignatureFamily K}
    {k n : ℕ} {f : Signature K (n+1)} (hf : Generated F k f) :
    Generated F k (fun x=>∑ b : Bool,f (Fin.snoc x b)) := by
  obtain ⟨P,hPF,hPk,hPf⟩ := hf
  refine ⟨P.sumLast,P.sumLast_uses hPF,P.sumLast_divisible hPk,?_⟩
  funext x
  rw [Presentation.sumLast_value,hPf]

/-- The empty ordered constraint list generates the constant one, with no
hidden variable and degree zero at every boundary position. -/
theorem generated_one {K : Type} [CommSemiring K] (F : SignatureFamily K) (k n : ℕ) :
    Generated F k (fun _ : Fin n → Bool=>(1 : K)) := by
  refine ⟨Presentation.power (fun _ : Fin n → Bool=>(1 : K)) 0,?_,
    Presentation.power_divisible _ (dvd_zero k),?_⟩
  · intro c
    exact Fin.elim0 c
  · funext x
    rw [Presentation.power_value,pow_zero]

/-- Every ordinary natural power is generated by actual repeated disjoint
products, including power zero. -/
theorem generated_pow {K : Type} [CommSemiring K] {F : SignatureFamily K}
    {k n : ℕ} {f : Signature K n} (hf : Generated F k f) (q : ℕ) :
    Generated F k (fun x=>f x^q) := by
  induction q with
  | zero => simpa only [pow_zero] using generated_one F k n
  | succ q ih => simpa only [pow_succ] using generated_hadamard ih hf

end
end Paper2.DegreeCSP
