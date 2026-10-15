import Paper2.SourceFaithful.SourceStatements.PhaseProductBlockClosure

/-! Literal one-port orientation and two-block contraction. The exact
nonzero coefficient used to orient each block is retained. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductClosure
noncomputable section
open Paper2 Tractable HeightOne.PhaseCards
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable
variable {I J : Type} [Fintype I] [Fintype J]

abbrev SingleRemaining (i : I) := {j : I // j ≠ i}

def singleSplit (i : I) : I ≃ SingleRemaining i ⊕ Unit where
  toFun j := if h : j=i then .inr () else .inl ⟨j,h⟩
  invFun := Sum.elim Subtype.val (fun _ => i)
  left_inv j := by by_cases h : j=i <;> simp [h]
  right_inv q := by cases q with
    | inl j => simp [j.property]
    | inr u => cases u; simp

omit [Fintype I] in
@[simp] theorem singleSplit_selected (i : I) : singleSplit i i = .inr () := by
  simp [singleSplit]

theorem singleSplit_card (i : I) : Fintype.card (SingleRemaining i)+1=Fintype.card I := by
  simpa using (Fintype.card_congr (singleSplit i)).symm

theorem block_pointed_form {N n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : EvenPhaseBlock N f) (i : Fin n) :
    ∃ (k : ℕ) (a : SingleRemaining i → Bool) (r c : AlgebraicComplex),
      Fintype.card (SingleRemaining i)=2*k+1 ∧ PhaseRatio N (k+1) r ∧ c≠0 ∧
      Tensor.reindex (singleSplit i) f =
        c • twoPoint (Sum.elim a (fun _ : Unit => false)) r := by
  rcases hf with ⟨k,a,r,hn,hr,rfl⟩
  have hc := singleSplit_card i
  have hcard : Fintype.card (SingleRemaining i)=2*k+1 := by
    have hcc : Fintype.card (SingleRemaining i)+1 = (2*k+1)+1 := by
      calc
        Fintype.card (SingleRemaining i)+1 = Fintype.card (Fin n) := by
          convert hc using 1
          congr 1
          congr 1
          exact Subsingleton.elim _ _
        _ = n := Fintype.card_fin n
        _ = 2*(k+1) := hn
        _ = 2*k+1+1 := by omega
    exact Nat.add_right_cancel hcc
  have he : (fun j => a ((singleSplit i).symm j)) =
      Sum.elim (fun j : SingleRemaining i => a j.val) (fun _ : Unit => a i) := by
    funext q; cases q <;> rfl
  rw [reindex_twoPoint,he]
  cases hb : a i with
  | false =>
    refine ⟨k,(fun j => a j.val),r,1,hcard,hr,one_ne_zero,?_⟩
    simp
  | true =>
    refine ⟨k,(fun j => !(a j.val)),r⁻¹,r,hcard,hr.inv,hr.ne_zero,?_⟩
    rw [twoPoint_complement _ r hr.ne_zero]
    congr 2
    funext q
    cases q <;> simp

def crossOrder : ((I ⊕ Unit) ⊕ (J ⊕ Unit)) ≃ ((I ⊕ J) ⊕ Bool) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr _) => .inr false
    | .inr (.inl j) => .inl (.inr j)
    | .inr (.inr _) => .inr true
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr j) => .inr (.inl j)
    | .inr false => .inl (.inr ())
    | .inr true => .inr (.inr ())
  left_inv q := by rcases q with (i|u)|(j|u) <;> rfl
  right_inv q := by rcases q with (i|j)|b <;> first | rfl | cases b <;> rfl

theorem crossOrder_tensor (a : I → Bool) (b : J → Bool) (r t : AlgebraicComplex) :
    Tensor.reindex crossOrder
      (Tensor.tensor (twoPoint (Sum.elim a (fun _ : Unit => false)) r)
        (twoPoint (Sum.elim b (fun _ : Unit => false)) t)) = cross a b r t := by
  funext x
  change twoPoint _ r _ * twoPoint _ t _ = twoPoint _ r _ * twoPoint _ t _
  congr 1 <;> congr 1 <;> funext q <;> cases q <;> rfl

theorem cross_plus_member {N k l : ℕ} (a : I → Bool) (b : J → Bool)
    (r t : AlgebraicComplex) (hi : Fintype.card I=2*k+1) (hj : Fintype.card J=2*l+1)
    (hr : PhaseRatio N (k+1) r) (ht : PhaseRatio N (l+1) t)
    (s : rootsOfUnity N AlgebraicComplex) :
    PhaseProduct N (contractKernel (plusKernel (s.val : AlgebraicComplex)) (cross a b r t)) := by
  rw [cross_plus]
  apply twoPoint_member (k:=k+l)
  · rw [Fintype.card_sum,hi,hj]; omega
  · exact hr.merge_blocks ht s

theorem cross_minus_member {N k l : ℕ} (a : I → Bool) (b : J → Bool)
    (r t : AlgebraicComplex) (hi : Fintype.card I=2*k+1) (hj : Fintype.card J=2*l+1)
    (hr : PhaseRatio N (k+1) r) (ht : PhaseRatio N (l+1) t)
    (s : rootsOfUnity N AlgebraicComplex) :
    PhaseProduct N (contractKernel (minusKernel (s.val : AlgebraicComplex)) (cross a b r t)) := by
  rw [cross_minus _ _ _ _ _ ht.ne_zero]
  apply PhaseProduct.scale
  apply twoPoint_member (k:=k+l)
  · rw [Fintype.card_sum,hi,hj]; omega
  · exact hr.merge_blocks_inverse ht s

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductClosure

