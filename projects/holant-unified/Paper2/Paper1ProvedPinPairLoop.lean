import Paper2.Paper1ProvedPinDeletionSubstitution

/-! Ordered two-port operations for support descent. pairLoop closes the two
specified ports by a physical native X self-loop. pairPin fixes those same
ports by two actual unit-pin caps. Both retain the remaining double-succAbove
order, and substitution inlines any previously constructed source graph. -/
namespace Paper2.Paper1Proved.PinPairLoop
open Paper2.Tractable Paper2.ExactInput
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
variable {n : ℕ}

def pairWord (i : Fin (n+2)) (j : Fin (n+1)) (b : Bool) (y : Fin n → Bool) :
    Fin (n+2) → Bool := Fin.insertNth i b (Fin.insertNth j (!b) y)

def pairLoop {K : Type} [Add K] (f : Signature K (n+2)) (i : Fin (n+2)) (j : Fin (n+1)) :
    Signature K n := fun y => f (pairWord i j false y)+f (pairWord i j true y)

def pairPin {K : Type} (f : Signature K (n+2)) (i : Fin (n+2)) (j : Fin (n+1))
    (b c : Bool) : Signature K n :=
  fun y => f (Fin.insertNth i b (Fin.insertNth j c y))

def ports (i : Fin (n+2)) (j : Fin (n+1)) :
    (Σ _ : Unit, Fin (n+2)) ≃ (Fin n ⊕ (Unit × Bool)) where
  toFun p := Fin.insertNth (α := fun _ => Fin n ⊕ (Unit × Bool)) i (.inr ((),false))
    (Fin.insertNth (α := fun _ => Fin n ⊕ (Unit × Bool)) j (.inr ((),true))
      (fun k => .inl k)) p.2
  invFun p := match p with
    | .inl k => ⟨(),i.succAbove (j.succAbove k)⟩
    | .inr (_,false) => ⟨(),i⟩
    | .inr (_,true) => ⟨(),i.succAbove j⟩
  left_inv := by
    rintro ⟨u,k⟩
    cases u
    induction k using i.succAboveCases
    · simp
    · rename_i l
      induction l using j.succAboveCases <;> simp
  right_inv := by
    rintro (k | ⟨u,b⟩)
    · simp
    · cases u
      cases b <;> simp

def finite (f : Signature AlgebraicComplex (n+2)) (i : Fin (n+2)) (j : Fin (n+1)) :
    FiniteNetwork AlgebraicComplex Unit Unit n where
  arity _ := n+2
  ports := ports i j
  vertex _ := f
  edge _ := Signature.disequality

theorem finite_denote (f : Signature AlgebraicComplex (n+2)) (i : Fin (n+2))
    (j : Fin (n+1)) : (finite f i j).denote=pairLoop f i j := by
  letI : DecidableEq Unit := fun _ _ => Classical.propDecidable _
  funext a
  have he : (finite f i j).denote a=∑ b : Bool, f (pairWord i j b a) := by
    rw [FiniteNetwork.denote_nativeX _ (by intro e; rfl)]
    apply Fintype.sum_equiv (Equiv.funUnique Unit Bool)
    intro z
    rw [Fintype.prod_unique]
    change f (fun k => Sum.elim a
      (fun q : Unit × Bool => if q.2 then !(z q.1) else z q.1)
        ((ports i j) ⟨(),k⟩))=f (pairWord i j (z ()) a)
    apply congrArg f
    funext k
    induction k using i.succAboveCases
    · simp [ports,pairWord]
    · rename_i l
      induction l using j.succAboveCases <;> simp [ports,pairWord]
  rw [he]
  simp [Fintype.sum_bool,pairLoop,add_comm]

theorem pairLoop_realizable_of_realizable_family (F : SignatureFamily AlgebraicComplex)
    (f : Signature AlgebraicComplex (n+2)) (i : Fin (n+2)) (j : Fin (n+1))
    (hf : NetworkRealizable F f) : NetworkRealizable F (pairLoop f i j) := by
  let G := (finite f i j).toNetwork
  have hg := NetworkRealizable.substitute G (by intro e; rfl) (by intro v; exact hf)
  have hd : G.denote=pairLoop f i j := by
    dsimp only [G]
    rw [FiniteNetwork.denote_toNetwork,finite_denote]
  exact hd ▸ hg

theorem pairLoop_realizable_family (F : SignatureFamily AlgebraicComplex)
    (f : Signature AlgebraicComplex (n+2)) (i : Fin (n+2)) (j : Fin (n+1))
    (hf : (⟨n+2,f⟩ : AnySignature AlgebraicComplex) ∈ F) :
    NetworkRealizable F (pairLoop f i j) :=
  pairLoop_realizable_of_realizable_family F f i j (PinDeletion.member_realizable_family F f hf)

theorem pairLoop_realizable_of_realizable (L : Language)
    (f : Signature AlgebraicComplex (n+2)) (i : Fin (n+2)) (j : Fin (n+1))
    (hf : NetworkRealizable L.family f) : NetworkRealizable L.family (pairLoop f i j) :=
  pairLoop_realizable_of_realizable_family L.family f i j hf

theorem pairPin_realizable_of_realizable_family (F : SignatureFamily AlgebraicComplex)
    (f : Signature AlgebraicComplex (n+2)) (i : Fin (n+2)) (j : Fin (n+1)) (b c : Bool)
    (hf : NetworkRealizable F f)
    (hb : (⟨1,TensorDecomposition.literalPin (!b)⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hc : (⟨1,TensorDecomposition.literalPin (!c)⟩ : AnySignature AlgebraicComplex) ∈ F) :
    NetworkRealizable F (pairPin f i j b c) := by
  have h1 := PinDeletion.pinCoordinate_of_realizable_family F f i b hf hb
  have h2 := PinDeletion.pinCoordinate_of_realizable_family F (PinDeletion.pinCoordinate f i b) j c h1 hc
  exact h2

end
end Paper2.Paper1Proved.PinPairLoop
