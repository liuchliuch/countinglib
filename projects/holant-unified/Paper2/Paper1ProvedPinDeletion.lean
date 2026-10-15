import Paper2.Paper1ProvedPinCoordinate

/-! Fix one source coordinate and preserve the increasing order of all other
ports. One opposite literal unit pin is joined by one native X edge. This
physical graph implements Fin.insertNth exactly, even for a nullary result. -/
namespace Paper2.Paper1Proved.PinDeletion
open Paper2.Tractable Paper2.ExactInput
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
variable {n : ℕ}

def pinCoordinate {K : Type} (f : Signature K (n+1)) (i : Fin (n+1)) (b : Bool) :
    Signature K n := fun y => f (Fin.insertNth i b y)

abbrev arity : Bool → ℕ
  | false => n+1
  | true => 1

def ports (i : Fin (n+1)) : (Σ v : Bool, Fin (arity (n := n) v)) ≃
    (Fin n ⊕ (Unit × Bool)) where
  toFun p := match p with
    | ⟨false,k⟩ => Fin.insertNth (α := fun _ => Fin n ⊕ (Unit × Bool)) i
        (.inr ((),false)) (fun j => .inl j) k
    | ⟨true,_⟩ => .inr ((),true)
  invFun p := match p with
    | .inl j => ⟨false,i.succAbove j⟩
    | .inr (_,false) => ⟨false,i⟩
    | .inr (_,true) => ⟨true,(0 : Fin 1)⟩
  left_inv := by
    rintro ⟨v,k⟩
    cases v with
    | false => induction k using i.succAboveCases <;> simp
    | true => have hk : k=(0 : Fin 1) := Fin.eq_zero k; subst k; rfl
  right_inv := by
    rintro (j | ⟨u,b⟩)
    · simp
    · cases u
      cases b <;> simp

def finite (f : Signature AlgebraicComplex (n+1)) (i : Fin (n+1)) (b : Bool) :
    FiniteNetwork AlgebraicComplex Bool Unit n where
  arity := arity
  ports := ports i
  vertex v := match v with
    | false => f
    | true => TensorDecomposition.literalPin (!b)
  edge _ := Signature.disequality

def assignment (b : Bool) : (Unit × Bool) → Bool := fun p => if p.2 then !b else b

def factor (b : Bool) (z : (Unit × Bool) → Bool) : AlgebraicComplex :=
  TensorDecomposition.literalPin (!b) (fun _ => z ((),true)) *
    Signature.disequality (z ((),false)) (z ((),true))

theorem factor_eq (b : Bool) (z : (Unit × Bool) → Bool) :
    factor b z = if z ((),false)=b ∧ z ((),true)=!b then 1 else 0 := by
  cases b <;> cases hf : z ((),false) <;> cases ht : z ((),true) <;>
    simp [factor,TensorDecomposition.literalPin,Signature.disequality,hf,ht]

theorem factor_assignment (b : Bool) : factor b (assignment b)=1 := by
  simp [factor_eq,assignment]

theorem factor_zero (b : Bool) (z : (Unit × Bool) → Bool) (hz : z≠assignment b) :
    factor b z=0 := by
  have hn : ¬ (z ((),false)=b ∧ z ((),true)=!b) := by
    rintro ⟨h0,h1⟩
    apply hz
    funext p
    rcases p with ⟨u,k⟩
    cases u
    cases k <;> assumption
  simp [factor_eq,hn]

theorem finite_denote (f : Signature AlgebraicComplex (n+1)) (i : Fin (n+1)) (b : Bool) :
    (finite f i b).denote=pinCoordinate f i b := by
  funext a
  have he : (finite f i b).denote a =
      ∑ z : (Unit × Bool) → Bool, f (Fin.insertNth i (z ((),false)) a)*factor b z := by
    dsimp only [FiniteNetwork.denote,finite]
    apply Finset.sum_congr (by ext z; simp)
    intro z _
    rw [Fintype.prod_bool]
    dsimp only
    have hw : (fun k : Fin (n+1) => Sum.elim a z ((ports i) ⟨false,k⟩))=
        Fin.insertNth i (z ((),false)) a := by
      funext k
      induction k using i.succAboveCases <;> simp [ports]
    rw [hw]
    change (TensorDecomposition.literalPin (!b) (fun _ => z ((),true)) *
      f (Fin.insertNth i (z ((),false)) a)) *
        (∏ e : Unit, Signature.disequality (z (e,false)) (z (e,true))) = _
    rw [Fintype.prod_unique]
    change _ = f (Fin.insertNth i (z ((),false)) a) *
      (TensorDecomposition.literalPin (!b) (fun _ => z ((),true)) *
        Signature.disequality (z ((),false)) (z ((),true)))
    ac_rfl
  rw [he,Finset.sum_eq_single (assignment b)]
  · simp [assignment,factor_assignment,pinCoordinate]
  · intro z _ hz
    rw [factor_zero b z hz,mul_zero]
  · simp

theorem pinCoordinate_realizable_family (F : SignatureFamily AlgebraicComplex)
    (f : Signature AlgebraicComplex (n+1)) (i : Fin (n+1)) (b : Bool)
    (hf : (⟨n+1,f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hpin : (⟨1,TensorDecomposition.literalPin (!b)⟩ : AnySignature AlgebraicComplex) ∈ F) :
    NetworkRealizable F (pinCoordinate f i b) := by
  let N := finite f i b
  refine ⟨n,N.toNetwork,Equiv.refl _,?_,?_,?_⟩
  · intro v
    change (⟨N.arity ((Fintype.equivFin Bool).symm v),
      N.vertex ((Fintype.equivFin Bool).symm v)⟩ : AnySignature AlgebraicComplex) ∈ F
    cases (Fintype.equivFin Bool).symm v with
    | false => exact hf
    | true => exact hpin
  · intro e
    rfl
  · rw [FiniteNetwork.denote_toNetwork]
    simpa only [Tensor.reindex_refl] using finite_denote f i b

theorem pinCoordinate_realizable (L : Language)
    (f : Signature AlgebraicComplex (n+1)) (i : Fin (n+1)) (b : Bool)
    (hf : (⟨n+1,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hpin : (⟨1,TensorDecomposition.literalPin (!b)⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    NetworkRealizable L.family (pinCoordinate f i b) :=
  pinCoordinate_realizable_family L.family f i b hf hpin

end
end Paper2.Paper1Proved.PinDeletion
