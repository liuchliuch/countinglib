import Paper2.DegreeCSP.OrderedPresentation
import Paper2.PrimeFactorization.PointMass

/-! Actual zero-pin padding for any ordered arity, including arity zero.
Each partial copy retains its selected boundary port and gives every other
port a fresh hidden variable with t literal pin constraints. All boundary
and hidden degrees are exactly t+1. -/
namespace Paper2.DegreeCSP.HigherArityPinPadding
open scoped BigOperators
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

abbrev Copy (n t : ℕ) := Fin n × Fin t
abbrev Hidden (n t : ℕ) := (p : Copy n t) × {j : Fin n // j≠p.1}
abbrev Tag (n t : ℕ) := Unit ⊕ (Copy n t ⊕ (Hidden n t × Fin t))

abbrev arity {n t : ℕ} : Tag n t → ℕ
  | Sum.inl _ => n
  | Sum.inr (Sum.inl _) => n
  | Sum.inr (Sum.inr _) => 1

abbrev table {n t : ℕ} (f : Signature AlgebraicComplex n) :
    (j : Tag n t) → Signature AlgebraicComplex (arity j)
  | Sum.inl _ => f
  | Sum.inr (Sum.inl _) => f
  | Sum.inr (Sum.inr _) => literalPin false

def partialScope {n t : ℕ} (p : Copy n t) (j : Fin n) : Fin n ⊕ Hidden n t :=
  if h : j=p.1 then Sum.inl p.1 else Sum.inr ⟨p,⟨j,h⟩⟩

abbrev scope {n t : ℕ} : (j : Tag n t) → Fin (arity j) → Fin n ⊕ Hidden n t
  | Sum.inl _, i => Sum.inl i
  | Sum.inr (Sum.inl p), i => partialScope p i
  | Sum.inr (Sum.inr p), _ => Sum.inr p.1

abbrev padded {n : ℕ} (f : Signature AlgebraicComplex n) (t : ℕ) :
    Presentation AlgebraicComplex (Fin n) :=
  OrderedPresentation.ordered (arity (n:=n) (t:=t)) (table f) scope

theorem partial_boundary_iff {n t : ℕ} (p : Copy n t) (j v : Fin n) :
    partialScope p j=Sum.inl v ↔ j=p.1 ∧ p.1=v := by
  by_cases selected : j=p.1
  · simp [partialScope,selected]
  · simp [partialScope,selected]

theorem partial_hidden_iff {n t : ℕ} (p : Copy n t) (j : Fin n) (v : Hidden n t) :
    partialScope p j=Sum.inr v ↔ p=v.1 ∧ j=v.2.val := by
  by_cases selected : j=p.1
  · simp only [partialScope,selected,dite_true,Sum.inl_ne_inr,false_iff]
    rintro ⟨equal,port⟩
    apply v.2.property
    exact port.symm.trans (congrArg Prod.fst equal)
  · simp only [partialScope,selected,dite_false,Sum.inr.injEq]
    constructor
    · intro equal
      exact ⟨congrArg Sigma.fst equal,congrArg (fun v : Hidden n t => v.2.val) equal⟩
    · rintro ⟨rfl,port⟩
      have eqSub : (⟨j,selected⟩ : {j : Fin n // j≠v.1.1})=v.2 := Subtype.ext port
      change (⟨v.1,⟨j,selected⟩⟩ : Hidden n t)=v
      rw [eqSub]

theorem partial_boundary_count {n t : ℕ} (p : Copy n t) (v : Fin n) :
    (∑ j : Fin n,if partialScope p j=Sum.inl v then (1 : ℕ) else 0)=
      if p.1=v then 1 else 0 := by
  simp_rw [partial_boundary_iff]
  by_cases equal : p.1=v <;> simp [equal]

theorem partial_hidden_count {n t : ℕ} (p : Copy n t) (v : Hidden n t) :
    (∑ j : Fin n,if partialScope p j=Sum.inr v then (1 : ℕ) else 0)=
      if p=v.1 then 1 else 0 := by
  simp_rw [partial_hidden_iff]
  by_cases equal : p=v.1 <;> simp [equal]

theorem boundary_degree {n : ℕ} (f : Signature AlgebraicComplex n) (t : ℕ) (v : Fin n) :
    (padded f t).degree (Sum.inl v)=t+1 := by
  classical
  change (padded f t).degree (OrderedPresentation.variableEquiv (Sum.inl v))=_
  rw [OrderedPresentation.ordered_degree]
  simp only [Fintype.sum_sum_type,arity,scope]
  simp_rw [partial_boundary_iff]
  simp only [Fintype.sum_prod_type]
  simp only [ite_and]
  simp
  simp only [apply_ite,Finset.card_univ,Fintype.card_fin,Finset.card_empty]
  simp [Nat.add_comm]

theorem hidden_degree {n : ℕ} (f : Signature AlgebraicComplex n) (t : ℕ) (v : Hidden n t) :
    (padded f t).degree (OrderedPresentation.variableEquiv (Sum.inr v))=t+1 := by
  classical
  rw [OrderedPresentation.ordered_degree]
  simp only [Fintype.sum_sum_type,arity,scope]
  simp_rw [partial_hidden_iff]
  simp only [Fintype.sum_prod_type]
  rcases v with ⟨⟨vi,vt⟩,vj⟩
  simp [Prod.mk.injEq,ite_and,Finset.sum_ite_irrel,Nat.add_comm]

theorem divisible {n : ℕ} (f : Signature AlgebraicComplex n) (t : ℕ) :
    (padded f t).DegreeDivisible (t+1) := by
  intro v
  obtain ⟨w,rfl⟩ := OrderedPresentation.variableEquiv.surjective v
  cases w with
  | inl w =>
      change t+1 ∣ (padded f t).degree (Sum.inl w)
      rw [boundary_degree]
  | inr w => rw [hidden_degree]

theorem uses (F : SignatureFamily AlgebraicComplex) {n : ℕ}
    (f : Signature AlgebraicComplex n) (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hp : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex) ∈ F) (t : ℕ) :
    (padded f t).Uses F := by
  apply OrderedPresentation.ordered_uses
  intro j
  cases j with
  | inl _ => exact hf
  | inr j => cases j with
    | inl _ => exact hf
    | inr _ => exact hp

theorem partial_value {n t : ℕ} (x : Fin n → Bool) (p : Copy n t) :
    (fun i => Sum.elim x (fun _ => false) (partialScope p i))=
      Function.update (fun _ => false) p.1 (x p.1) := by
  funext i
  by_cases equal : i=p.1 <;> simp [partialScope,Function.update,equal]

theorem value {n : ℕ} (f : Signature AlgebraicComplex n) {t : ℕ} (ht : 0<t)
    (x : Fin n → Bool) :
    (padded f t).value x=f x*∏ i : Fin n,
      (f (Function.update (fun _ => false) i (x i)))^t := by
  calc
    _= ∏ j : Tag n t,table f j
        (fun i => Sum.elim x (fun _ => false) (scope j i)) := by
      rw [OrderedPresentation.ordered_value]
      apply Finset.sum_eq_single (fun _ => false)
      · intro y _ hy
        have bad : ∃ p,y p≠false := by
          by_contra none
          apply hy
          funext p
          exact not_not.mp (not_exists.mp none p)
        obtain ⟨p,hp⟩ := bad
        apply Finset.prod_eq_zero
          (Finset.mem_univ (Sum.inr (Sum.inr (p,(⟨0,ht⟩ : Fin t)))))
        simp [table,scope,literalPin,hp]
      · simp
    _= _ := by
      have root (j : Unit) : table f (t:=t) (Sum.inl j)
          (fun i => Sum.elim x (fun _ => false) (scope (Sum.inl j) i))=f x := rfl
      have piece (p : Copy n t) : table f (Sum.inr (Sum.inl p))
          (fun i => Sum.elim x (fun _ => false) (scope (Sum.inr (Sum.inl p)) i))=
            f (Function.update (fun _ => false) p.1 (x p.1)) := by
        exact congrArg f (partial_value x p)
      have pin (p : Hidden n t × Fin t) : table f (Sum.inr (Sum.inr p))
          (fun i => Sum.elim x (fun _ => false) (scope (Sum.inr (Sum.inr p)) i))=1 := by
        simp
      simp only [Fintype.prod_sum_type]
      simp_rw [root,piece,pin]
      have card : (Finset.univ : Finset (Fin t)).card=t := Fintype.card_fin t
      simp [Fintype.prod_prod_type,Finset.prod_const,card]

/-- The witness has the literal original constraints and all actual pins;
it remains valid for the nullary original signature. -/
theorem generated (F : SignatureFamily AlgebraicComplex) {n : ℕ}
    (f : Signature AlgebraicComplex n) (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hp : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex) ∈ F)
    {t : ℕ} (ht : 0<t) :
    Generated F (t+1) (fun x => f x*∏ i : Fin n,
      (f (Function.update (fun _ => false) i (x i)))^t) :=
  ⟨padded f t,uses F f hf hp t,divisible f t,funext (value f ht)⟩

end
end Paper2.DegreeCSP.HigherArityPinPadding

