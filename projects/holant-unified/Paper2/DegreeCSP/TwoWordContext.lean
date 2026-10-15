import Paper2.DegreeCSP.OrderedPresentation
import Paper2.PrimeFactorization.PointMass

/-! One exact two-word unary context. Forward differing ports use the boundary
once, reverse differing ports use k-1 actual X clauses, and fixed ports use
k-1 literal pins. Every hidden port has degree k; the boundary degree records
the signed occupied-weight difference modulo k. -/
namespace Paper2.DegreeCSP.TwoWordContext
open scoped BigOperators
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (x y : Fin n→Bool)

def Forward (i : Fin n) : Prop := x i=false ∧ y i=true
abbrev Hidden := {i : Fin n // ¬Forward x y i}
abbrev Fixed := {i : Fin n // x i=y i}
abbrev Reverse := {i : Fin n // x i=true ∧ y i=false}
abbrev Tag (t : ℕ) := Unit ⊕ ((Fixed x y × Fin t) ⊕ (Reverse x y × Fin t))

private theorem fixed_not_forward (i : Fixed x y) : ¬Forward x y i.val := by
  rintro ⟨hx,hy⟩
  have he := i.property
  rw [hx,hy] at he
  cases he

private theorem reverse_not_forward (i : Reverse x y) : ¬Forward x y i.val := by
  rintro ⟨hx,_⟩
  rw [i.property.1] at hx
  cases hx

def rootScope (i : Fin n) : Fin 1 ⊕ Hidden x y :=
  if h : Forward x y i then .inl 0 else .inr ⟨i,h⟩

abbrev arity {t : ℕ} : Tag x y t→ℕ
  | .inl _ => n
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

abbrev table {t : ℕ} (f : Signature AlgebraicComplex n) :
    (j : Tag x y t)→Signature AlgebraicComplex (arity x y j)
  | .inl _ => f
  | .inr (.inl p) => literalPin (x p.1.val)
  | .inr (.inr _) => kernelSignature (Signature.disequality (K:=AlgebraicComplex))

abbrev scope {t : ℕ} : (j : Tag x y t)→Fin (arity x y j)→Fin 1 ⊕ Hidden x y
  | .inl _,i => rootScope x y i
  | .inr (.inl p),_ => .inr ⟨p.1.val,fixed_not_forward x y p.1⟩
  | .inr (.inr p),j => if j=0 then .inr ⟨p.1.val,reverse_not_forward x y p.1⟩ else .inl 0

abbrev context (f : Signature AlgebraicComplex n) (t : ℕ) :
    Presentation AlgebraicComplex (Fin 1) :=
  OrderedPresentation.ordered (arity x y) (table x y f) (scope x y (t:=t))

theorem root_hidden_iff (i : Fin n) (h : Hidden x y) :
    rootScope x y i=Sum.inr h ↔ i=h.val := by
  by_cases hi : Forward x y i
  · simp only [rootScope,hi,dite_true,Sum.inl_ne_inr,false_iff]
    intro he
    subst i
    exact h.property hi
  · simp only [rootScope,hi,dite_false,Sum.inr.injEq]
    exact Subtype.ext_iff

theorem root_boundary_iff (i : Fin n) : rootScope x y i=Sum.inl (0 : Fin 1) ↔ Forward x y i := by
  by_cases hi : Forward x y i <;> simp [rootScope,hi]

theorem uses (F : SignatureFamily AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F)
    (hp0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (hp1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hX : (⟨2,kernelSignature (Signature.disequality (K:=AlgebraicComplex))⟩ : AnySignature AlgebraicComplex)∈F)
    (t : ℕ) : (context x y f t).Uses F := by
  apply OrderedPresentation.ordered_uses
  rintro (_ | (p | p))
  · exact hf
  · change (⟨1,literalPin (x p.1.val)⟩ : AnySignature AlgebraicComplex)∈F
    cases hx:x p.1.val
    · exact hp0
    · exact hp1
  · exact hX

private theorem fixedOrReverse (i : Hidden x y) : x i.val=y i.val ∨ (x i.val=true ∧ y i.val=false) := by
  have hi := i.property
  cases hx:x i.val <;> cases hy:y i.val <;> simp_all [Forward]

/-- The actual hidden assignment for one boundary bit is unique. -/
def chosen (b : Bool) (i : Hidden x y) : Bool := if x i.val=y i.val then x i.val else !b

abbrev rootWord (b : Bool) (h : Hidden x y→Bool) : Fin n→Bool :=
  fun i=>Sum.elim (fun _ : Fin 1=>b) h (rootScope x y i)

def background {t : ℕ} (b : Bool) (h : Hidden x y→Bool) : AlgebraicComplex :=
  (∏ p : Fixed x y×Fin t,literalPin (x p.1.val)
    (fun _=>h ⟨p.1.val,fixed_not_forward x y p.1⟩))*
  (∏ p : Reverse x y×Fin t,Signature.disequality (K:=AlgebraicComplex)
    (h ⟨p.1.val,reverse_not_forward x y p.1⟩) b)

private theorem chosen_rootWord (b : Bool) :
    rootWord x y b (chosen x y b)=(if b then y else x) := by
  funext i
  cases b <;> cases hx:x i <;> cases hy:y i <;>
    simp [rootWord,rootScope,Forward,chosen,hx,hy]

private theorem background_chosen (t : ℕ) (b : Bool) :
    background x y (t:=t) b (chosen x y b)=1 := by
  have hp (p : Fixed x y×Fin t) : literalPin (x p.1.val)
      (fun _=>chosen x y b ⟨p.1.val,fixed_not_forward x y p.1⟩)=1 := by
    simp [chosen,p.1.property,literalPin]
  have hx (p : Reverse x y×Fin t) : Signature.disequality (K:=AlgebraicComplex)
      (chosen x y b ⟨p.1.val,reverse_not_forward x y p.1⟩) b=1 := by
    have hi : x p.1.val≠y p.1.val := by
      rw [p.1.property.1,p.1.property.2]
      decide
    cases b <;> simp [chosen,hi,Signature.disequality]
  unfold background
  have hp' : (∏ p : Fixed x y×Fin t,literalPin (x p.1.val)
      (fun _=>chosen x y b ⟨p.1.val,fixed_not_forward x y p.1⟩))=1 :=
    Finset.prod_eq_one (fun p _=>hp p)
  have hx' : (∏ p : Reverse x y×Fin t,Signature.disequality (K:=AlgebraicComplex)
      (chosen x y b ⟨p.1.val,reverse_not_forward x y p.1⟩) b)=1 :=
    Finset.prod_eq_one (fun p _=>hx p)
  simpa only [mul_one] using congrArg₂ (·*·) hp' hx'

private theorem background_zero {t : ℕ} (ht : 0<t) (b : Bool) (h : Hidden x y→Bool)
    (hh : h≠chosen x y b) : background x y (t:=t) b h=0 := by
  have hex : ∃i,h i≠chosen x y b i := by
    by_contra none
    apply hh
    funext i
    by_contra hi
    exact none ⟨i,hi⟩
  obtain ⟨i,hi⟩ := hex
  rcases fixedOrReverse x y i with he | he
  · let p : Fixed x y×Fin t := (⟨i.val,he⟩,⟨0,ht⟩)
    have h0 : literalPin (x p.1.val)
        (fun _=>h ⟨p.1.val,fixed_not_forward x y p.1⟩)=0 := by
      have hbit : h i≠x i.val := by simpa only [chosen,he,ite_true] using hi
      change (if h i=x i.val then (1 : AlgebraicComplex) else 0)=0
      exact ite_eq_right (fun h=>hbit h)
    have hp : (∏ p : Fixed x y×Fin t,literalPin (x p.1.val)
        (fun _=>h ⟨p.1.val,fixed_not_forward x y p.1⟩))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ p) h0
    simp only [background,hp,zero_mul]
  · let p : Reverse x y×Fin t := (⟨i.val,he⟩,⟨0,ht⟩)
    have hneq : x i.val≠y i.val := by rw [he.1,he.2]; decide
    have hbit : h i≠!b := by simpa only [chosen,hneq,ite_false] using hi
    have h0 : Signature.disequality (K:=AlgebraicComplex) (h ⟨p.1.val,reverse_not_forward x y p.1⟩) b=0 := by
      change Signature.disequality (K:=AlgebraicComplex) (h i) b=0
      cases hb:b <;> cases hv:h i <;> simp_all [Signature.disequality]
    have hx : (∏ p : Reverse x y×Fin t,Signature.disequality (K:=AlgebraicComplex)
        (h ⟨p.1.val,reverse_not_forward x y p.1⟩) b)=0 :=
      Finset.prod_eq_zero (Finset.mem_univ p) h0
    unfold background
    rw [hx,mul_zero]

/-- Exact coefficients at both boundary bits, with no dropped scalar. -/
theorem value (f : Signature AlgebraicComplex n) {t : ℕ} (ht : 0<t) (b : Bool) :
    (context x y f t).value (fun _=>b)=f (if b then y else x) := by
  classical
  rw [OrderedPresentation.ordered_value]
  have he (h : Hidden x y→Bool) :
      (∏j:Tag x y t,table x y f j
        (fun i=>Sum.elim (fun _ : Fin 1=>b) h (scope x y j i)))=
      f (rootWord x y b h)*background x y (t:=t) b h := by
    simp only [Fintype.prod_sum_type,Fintype.prod_unique,arity,table,scope]
    congr 1
  simp_rw [he]
  rw [Finset.sum_eq_single (chosen x y b)]
  · rw [background_chosen,mul_one,chosen_rootWord]
  · intro h _ hh
    rw [background_zero x y ht b h hh,mul_zero]
  · simp

end
end Paper2.DegreeCSP.TwoWordContext
