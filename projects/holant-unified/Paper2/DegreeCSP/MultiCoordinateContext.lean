import Paper2.DegreeCSP.OrderedPresentation
import Paper2.DegreeCSP.PartialUnaryProducts
import Paper2.PrimeFactorization.PointMass

/-! An original constraint is used exactly once on fixed, selected and
complemented boundary coordinates. Every fixed port has literal pin caps;
every complemented port has literal X clauses. Thus the coefficients of
the original constraint are retained, without taking powers or discarding
signs. Hidden degrees are completed by repeated copies of these clauses. -/
namespace Paper2.DegreeCSP.MultiCoordinateContext
open scoped BigOperators
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

abbrev Expr (r : ℕ) := Bool ⊕ (Fin r×Bool)
def eval {r : ℕ} (e : Expr r) (x : Fin r→Bool) : Bool:=
  match e with
  | .inl b=>b
  | .inr (j,b)=>Bool.xor (x j) b

def word {n r : ℕ} (E : Fin n→Expr r) (x : Fin r→Bool) : Fin n→Bool:=
  fun i=>eval (E i) x

variable {n r : ℕ} (E : Fin n→Expr r)
def Positive (i : Fin n) : Prop:=∃j:Fin r,E i=Sum.inr (j,false)
abbrev Hidden := {i : Fin n // ¬Positive E i}
abbrev Fixed := {p : Fin n×Bool // E p.1=Sum.inl p.2}
abbrev Reverse := {p : Fin n×Fin r // E p.1=Sum.inr (p.2,true)}
abbrev Tag (t : ℕ) := Unit ⊕ ((Fixed E×Fin t) ⊕ (Reverse E×Fin t))

private theorem fixed_not_positive (p : Fixed E) : ¬Positive E p.val.1 := by
  rintro ⟨j,hj⟩
  rw [p.property] at hj
  cases hj

private theorem reverse_not_positive (p : Reverse E) : ¬Positive E p.val.1 := by
  rintro ⟨j,hj⟩
  rw [p.property] at hj
  have h := congrArg (fun x : Expr r=>x.getRight?.map Prod.snd) hj
  simp at h

def rootScope (i : Fin n) : Fin r ⊕ Hidden E:=
  if h : Positive E i then .inl (Classical.choose h) else .inr ⟨i,h⟩

theorem root_boundary_iff (i : Fin n) (j : Fin r) :
    rootScope E i=Sum.inl j ↔ E i=Sum.inr (j,false) := by
  by_cases h : Positive E i
  · simp only [rootScope,h,dite_true,Sum.inl.injEq]
    constructor
    · intro he
      simpa only [he] using Classical.choose_spec h
    · intro he
      have hc:=Classical.choose_spec h
      exact (Prod.mk.inj (Sum.inr.inj (he.symm.trans hc))).1.symm
  · simp only [rootScope,h,dite_false,Sum.inr_ne_inl,false_iff]
    exact fun he=>h ⟨j,he⟩

theorem root_hidden_iff (i : Fin n) (h : Hidden E) :
    rootScope E i=Sum.inr h ↔ i=h.val := by
  by_cases hi : Positive E i
  · simp only [rootScope,hi,dite_true,Sum.inl_ne_inr,false_iff]
    intro he
    subst i
    exact h.property hi
  · simp only [rootScope,hi,dite_false,Sum.inr.injEq]
    exact Subtype.ext_iff

abbrev arity {t : ℕ} : Tag E t→ℕ
  | .inl _=>n
  | .inr (.inl _)=>1
  | .inr (.inr _)=>2

abbrev table {t : ℕ} (f : Signature AlgebraicComplex n) :
    (j : Tag E t)→Signature AlgebraicComplex (arity E j)
  | .inl _=>f
  | .inr (.inl p)=>literalPin p.1.val.2
  | .inr (.inr _)=>kernelSignature Signature.disequality

abbrev scope {t : ℕ} : (j : Tag E t)→Fin (arity E j)→Fin r ⊕ Hidden E
  | .inl _,i=>rootScope E i
  | .inr (.inl p),_=>.inr ⟨p.1.val.1,fixed_not_positive E p.1⟩
  | .inr (.inr p),j=>if j=0 then
      .inr ⟨p.1.val.1,reverse_not_positive E p.1⟩ else .inl p.1.val.2

abbrev context (f : Signature AlgebraicComplex n) (t : ℕ) :
    Presentation AlgebraicComplex (Fin r):=
  OrderedPresentation.ordered (arity E) (table E f) (scope E (t:=t))

theorem uses (F : SignatureFamily AlgebraicComplex) (f : Signature AlgebraicComplex n)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (t : ℕ) : (context E f t).Uses F := by
  apply OrderedPresentation.ordered_uses
  rintro (_ | (p | p))
  · exact hf
  · change (⟨1,literalPin p.1.val.2⟩ : AnySignature AlgebraicComplex)∈F
    cases hb:p.1.val.2
    · exact h0
    · exact h1
  · exact hX

def chosen (x : Fin r→Bool) (h : Hidden E) : Bool:=word E x h.val
abbrev rootWord (x : Fin r→Bool) (h : Hidden E→Bool) : Fin n→Bool:=
  fun i=>Sum.elim x h (rootScope E i)

private theorem chosen_rootWord (x : Fin r→Bool) :
    rootWord E x (chosen E x)=word E x := by
  funext i
  by_cases hi:Positive E i
  · change Sum.elim x (chosen E x) (rootScope E i)=eval (E i) x
    simp only [rootScope,hi,dite_true,Sum.elim_inl]
    have he:=congrArg (fun e : Expr r=>eval e x) (Classical.choose_spec hi)
    simpa only [eval,Bool.xor_false] using he.symm
  · simp only [rootWord,rootScope,hi,dite_false,Sum.elim_inr,chosen]

def background {t : ℕ} (x : Fin r→Bool) (h : Hidden E→Bool) : AlgebraicComplex:=
  (∏p:Fixed E×Fin t,literalPin p.1.val.2
    (fun _=>h ⟨p.1.val.1,fixed_not_positive E p.1⟩))*
  (∏p:Reverse E×Fin t,Signature.disequality
    (h ⟨p.1.val.1,reverse_not_positive E p.1⟩) (x p.1.val.2))

private theorem background_chosen (t : ℕ) (x : Fin r→Bool) :
    background E (t:=t) x (chosen E x)=1 := by
  have hp (p : Fixed E×Fin t) : literalPin p.1.val.2
      (fun _=>chosen E x ⟨p.1.val.1,fixed_not_positive E p.1⟩)=1 := by
    simp [chosen,word,p.1.property,eval,literalPin]
  have hX (p : Reverse E×Fin t) : (Signature.disequality
      (chosen E x ⟨p.1.val.1,reverse_not_positive E p.1⟩) (x p.1.val.2) : AlgebraicComplex)=1 := by
    cases hx:x p.1.val.2 <;>
      simp [chosen,word,p.1.property,eval,hx,Signature.disequality]
  unfold background
  rw [Finset.prod_eq_one (fun p _=>hp p),Finset.prod_eq_one (fun p _=>hX p),one_mul]

private theorem hidden_fixed_or_reverse (h : Hidden E) :
    (∃b:Bool,E h.val=Sum.inl b) ∨ (∃j:Fin r,E h.val=Sum.inr (j,true)) := by
  cases he:E h.val with
  | inl b=>exact Or.inl ⟨b,rfl⟩
  | inr p=>
    rcases p with ⟨j,b⟩
    cases b
    · exact False.elim (h.property ⟨j,he⟩)
    · exact Or.inr ⟨j,rfl⟩

private theorem background_zero {t : ℕ} (ht : 0<t) (x : Fin r→Bool)
    (h : Hidden E→Bool) (hh : h≠chosen E x) : background E (t:=t) x h=0 := by
  have hex : ∃i,h i≠chosen E x i := by
    by_contra none
    apply hh
    funext i
    exact not_not.mp (not_exists.mp none i)
  obtain ⟨i,hi⟩:=hex
  rcases hidden_fixed_or_reverse E i with ⟨b,hb⟩|⟨j,hj⟩
  · let p : Fixed E×Fin t:=(⟨(i.val,b),hb⟩,⟨0,ht⟩)
    have hz : literalPin p.1.val.2
        (fun _=>h ⟨p.1.val.1,fixed_not_positive E p.1⟩)=0 := by
      have he : h i≠b := by simpa [chosen,word,hb,eval] using hi
      simp [p,literalPin,he]
    have hp : (∏p:Fixed E×Fin t,literalPin p.1.val.2
        (fun _=>h ⟨p.1.val.1,fixed_not_positive E p.1⟩))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ p) hz
    simp only [background,hp,zero_mul]
  · let p : Reverse E×Fin t:=(⟨(i.val,j),hj⟩,⟨0,ht⟩)
    have hz : (Signature.disequality
        (h ⟨p.1.val.1,reverse_not_positive E p.1⟩) (x p.1.val.2) : AlgebraicComplex)=0 := by
      have he : h i≠Bool.xor (x j) true := by simpa [chosen,word,hj,eval] using hi
      change (Signature.disequality (h i) (x j) : AlgebraicComplex)=0
      cases hv:h i <;> cases hx:x j <;> simp_all [Signature.disequality]
    have hX : (∏p:Reverse E×Fin t,(Signature.disequality
        (h ⟨p.1.val.1,reverse_not_positive E p.1⟩) (x p.1.val.2) : AlgebraicComplex))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ p) hz
    exact mul_eq_zero_of_right _ hX

theorem value (f : Signature AlgebraicComplex n) {t : ℕ} (ht : 0<t) (x : Fin r→Bool) :
    (context E f t).value x=f (word E x) := by
  rw [OrderedPresentation.ordered_value]
  have he (h : Hidden E→Bool) :
      (∏j:Tag E t,table E f j (fun i=>Sum.elim x h (scope E j i)))=
      f (rootWord E x h)*background E (t:=t) x h := by
    simp only [Fintype.prod_sum_type,Fintype.prod_unique,arity,table,scope]
    congr 1
  simp_rw [he]
  rw [Finset.sum_eq_single (chosen E x)]
  · rw [background_chosen,mul_one,chosen_rootWord]
  · intro h _ hh
    rw [background_zero E ht x h hh,mul_zero]
  · simp

end
end Paper2.DegreeCSP.MultiCoordinateContext

