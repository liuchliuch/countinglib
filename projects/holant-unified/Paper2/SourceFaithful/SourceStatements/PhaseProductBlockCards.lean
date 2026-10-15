import Paper2.SourceFaithful.SourceStatements.PhaseProductPortTransport
import Paper2.SourceFaithful.SourceStatements.PhaseProductPointedBlocks
import Paper2.SourceFaithful.SourceStatements.PhaseProductSameBlock

/-! Every local block contraction on its actual named ports. The two-block
case orients each selected port before using the exact bilinear formula. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductClosure
noncomputable section
open Paper2 Tractable HeightOne.PhaseCards EndpointSelfLoop
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 10000
attribute [local instance] Classical.propDecidable

structure LocalRule (N : ℕ) (E : Kernel AlgebraicComplex) : Prop where
  same : ∀ {I : Type} [Fintype I] {k : ℕ}, Fintype.card I=2*k →
    ∀ (a : I → Bool) (p : Bool → Bool) (r : AlgebraicComplex),
      PhaseRatio N (k+1) r → PhaseProduct N (contractKernel E (twoPoint (Sum.elim a p) r))
  cross : ∀ {I J : Type} [Fintype I] [Fintype J] {k l : ℕ},
    ∀ (a : I → Bool) (b : J → Bool) (r t : AlgebraicComplex),
      Fintype.card I=2*k+1 → Fintype.card J=2*l+1 →
      PhaseRatio N (k+1) r → PhaseRatio N (l+1) t →
      PhaseProduct N (contractKernel E (PhaseProductClosure.cross a b r t))

theorem plus_rule {N : ℕ} (s : rootsOfUnity N AlgebraicComplex) :
    LocalRule N (plusKernel s.val) :=
  ⟨fun h a p r hr => same_plus h a p r hr s,
    fun a b r t hi hj hr ht => cross_plus_member a b r t hi hj hr ht s⟩

theorem minus_rule {N : ℕ} (s : rootsOfUnity N AlgebraicComplex) :
    LocalRule N (minusKernel s.val) :=
  ⟨fun h a p r hr => same_minus h a p r hr s,
    fun a b r t hi hj hr ht => cross_minus_member a b r t hi hj hr ht s⟩

theorem block_card {N n : ℕ} {E : Kernel AlgebraicComplex} (rule : LocalRule N E)
    (f : Signature AlgebraicComplex n) (hf : EvenPhaseBlock N f)
    (a b : Fin n) (hab : a≠b) : PhaseProduct N (card E a b hab f) := by
  rcases hf with ⟨k,w,r,hn,hr,rfl⟩
  have hc := Fintype.card_congr (splitPorts a b hab)
  have hcard : Fintype.card (Remaining a b)=2*k := by
    have hcc : Fintype.card (Remaining a b)+2=n := by
      simpa only [Fintype.card_sum,Fintype.card_bool,Fintype.card_fin] using hc.symm
    have heq : Fintype.card (Remaining a b)+2=2*k+2 := by
      calc
        Fintype.card (Remaining a b)+2=n := hcc
        _=2*(k+1) := hn
        _=2*k+2 := by omega
    exact Nat.add_right_cancel heq
  let wa : Remaining a b → Bool := fun i => w ((splitPorts a b hab).symm (.inl i))
  let wp : Bool → Bool := fun q => w ((splitPorts a b hab).symm (.inr q))
  have hw : (fun i => w ((splitPorts a b hab).symm i))=Sum.elim wa wp := by
    funext i; cases i <;> rfl
  unfold card
  rw [reindex_twoPoint,hw]
  exact rule.same hcard wa wp r hr

theorem pointed_pair_shape {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (f : Tensor AlgebraicComplex I) (g : Tensor AlgebraicComplex J)
    (a : I) (b : J) (w : SingleRemaining a → Bool) (v : SingleRemaining b → Bool)
    (r t c d : AlgebraicComplex)
    (hf : Tensor.reindex (singleSplit a) f=c•twoPoint (Sum.elim w (fun _ : Unit => false)) r)
    (hg : Tensor.reindex (singleSplit b) g=d•twoPoint (Sum.elim v (fun _ : Unit => false)) t) :
    Tensor.reindex ((Equiv.sumCongr (singleSplit a) (singleSplit b)).trans crossOrder)
      (Tensor.tensor f g) = (c*d)•cross w v r t := by
  have hs : Tensor.reindex (Equiv.sumCongr (singleSplit a) (singleSplit b))
      (Tensor.tensor f g) = Tensor.tensor (Tensor.reindex (singleSplit a) f)
        (Tensor.reindex (singleSplit b) g) := rfl
  rw [← Tensor.reindex_trans,hs,hf,hg]
  have hm : Tensor.tensor (c•twoPoint (Sum.elim w (fun _ : Unit => false)) r)
      (d•twoPoint (Sum.elim v (fun _ : Unit => false)) t) =
      (c*d)•Tensor.tensor (twoPoint (Sum.elim w (fun _ : Unit => false)) r)
        (twoPoint (Sum.elim v (fun _ : Unit => false)) t) := by
    funext x
    simp only [Tensor.tensor_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [hm]
  have he := crossOrder_tensor w v r t
  exact congrArg (fun z => (c*d)•z) he

theorem two_block_card {N m n : ℕ} {E : Kernel AlgebraicComplex} (rule : LocalRule N E)
    (f : Signature AlgebraicComplex m) (g : Signature AlgebraicComplex n)
    (hf : EvenPhaseBlock N f) (hg : EvenPhaseBlock N g) (a : Fin m) (b : Fin n) :
    PhaseProduct N (card E (Sum.inl a) (Sum.inr b) (by simp) (Tensor.tensor f g)) := by
  obtain ⟨k,w,r,c,hk,hr,hc,hf'⟩ := block_pointed_form f hf a
  obtain ⟨l,v,t,d,hl,ht,hd,hg'⟩ := block_pointed_form g hg b
  let e := (Equiv.sumCongr (singleSplit a) (singleSplit b)).trans crossOrder
  have hea : e (.inl a)=.inr false := by simp [e,crossOrder,singleSplit]
  have heb : e (.inr b)=.inr true := by simp [e,crossOrder,singleSplit]
  apply (card_membership_reindex E e (.inl a) (.inr b) (by simp) (Tensor.tensor f g)).mp
  have hout : PhaseProduct N (card E (.inr false) (.inr true) (by simp)
      (Tensor.reindex e (Tensor.tensor f g))) := by
    have hshape := pointed_pair_shape f g a b w v r t c d hf' hg'
    rw [hshape,card_scale,card_exposed]
    exact ((rule.cross w v r t hk hl hr ht).reindex exposedRemaining).scale (c*d)
  exact (card_membership_ports E (Tensor.reindex e (Tensor.tensor f g))
    _ (by simp) hea heb).mpr hout

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductClosure

