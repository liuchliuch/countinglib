import Paper2.SourceFaithful.SourceStatements.PhaseProductBlockClosure

/-! Ordered port transport for literal bilinear contractions. All surviving
ports are retained by explicit equivalences; no closure hypothesis is used. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductClosure
open Paper2.HeightOne Paper2.HeightOne.PhaseCards Paper2.EndpointSelfLoop
open Paper2.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

variable {I J R : Type} [Fintype I] [Fintype J] [Fintype R]

def remainingCongr (e : I ≃ J) (a b : I) : Remaining a b ≃ Remaining (e a) (e b) where
  toFun p := ⟨e p.1,fun h => p.2.1 (e.injective h),fun h => p.2.2 (e.injective h)⟩
  invFun q := ⟨e.symm q.1,
    fun h => q.2.1 (by simpa only [h] using (e.apply_symm_apply q.1).symm),
    fun h => q.2.2 (by simpa only [h] using (e.apply_symm_apply q.1).symm)⟩
  left_inv p := by apply Subtype.ext; exact e.symm_apply_apply p.1
  right_inv q := by apply Subtype.ext; exact e.apply_symm_apply q.1

omit [Fintype I] [Fintype J] in
theorem splitPorts_congr (e : I ≃ J) (a b : I) (hab : a ≠ b) (i : I) :
    splitPorts (e a) (e b) (e.injective.ne hab) (e i) =
      Sum.map (remainingCongr e a b) (fun t => t) (splitPorts a b hab i) := by
  by_cases ha : i=a
  · subst i; simp [splitPorts]
  by_cases hb : i=b
  · subst i; simp [splitPorts,Ne.symm hab]
  have hea : e i≠e a := fun h => ha (e.injective h)
  have heb : e i≠e b := fun h => hb (e.injective h)
  simp [splitPorts,ha,hb,hea,heb,remainingCongr]

omit [Fintype I] [Fintype J] in
theorem card_reindex (E : Kernel AlgebraicComplex) (e : I ≃ J)
    (a b : I) (hab : a ≠ b) (f : Tensor AlgebraicComplex I) :
    card E (e a) (e b) (e.injective.ne hab) (Tensor.reindex e f) =
      Tensor.reindex (remainingCongr e a b) (card E a b hab f) := by
  funext x
  unfold card contractKernel
  simp only [Tensor.reindex_apply]
  apply Finset.sum_congr rfl
  intro v _
  congr 2
  funext i
  rw [splitPorts_congr e a b hab i]
  cases splitPorts a b hab i <;> rfl

theorem card_four (E : Kernel AlgebraicComplex) (a b : I) (hab : a ≠ b)
    (f : Tensor AlgebraicComplex I) (x : Remaining a b → Bool) :
    card E a b hab f x =
      E false false*f (extendBits a b hab x false false) +
      E false true*f (extendBits a b hab x false true) +
      E true false*f (extendBits a b hab x true false) +
      E true true*f (extendBits a b hab x true true) := by
  have h01 : (fun q : Bool => if q then true else false) = (fun q => q) := by
    funext q; cases q <;> rfl
  have h10 : (fun q : Bool => if q then false else true) = (fun q => !q) := by
    funext q; cases q <;> rfl
  unfold extendBits
  simpa only [card,Tensor.reindex_apply,ite_self,h01,h10] using
    contractKernel_four E (Tensor.reindex (splitPorts a b hab) f) x

def remainingTensorLeft (a b : I) :
    (Remaining a b ⊕ J) ≃ Remaining (Sum.inl a : I ⊕ J) (Sum.inl b) where
  toFun
    | .inl p => ⟨.inl p.1,fun h => p.2.1 (Sum.inl.inj h),
        fun h => p.2.2 (Sum.inl.inj h)⟩
    | .inr j => ⟨.inr j,by simp⟩
  invFun := by
    rintro ⟨i,hi⟩
    cases i with
    | inl i => exact .inl ⟨i,fun h => hi.1 (congrArg Sum.inl h),
        fun h => hi.2 (congrArg Sum.inl h)⟩
    | inr j => exact .inr j
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨i,hi⟩; cases i <;> rfl

theorem card_tensor_left (E : Kernel AlgebraicComplex)
    (a b : I) (hab : a ≠ b) (f : Tensor AlgebraicComplex I) (g : Tensor AlgebraicComplex J) :
    card E (.inl a) (.inl b) (fun h => hab (Sum.inl.inj h)) (Tensor.tensor f g) =
      Tensor.reindex (remainingTensorLeft a b) (Tensor.tensor (card E a b hab f) g) := by
  funext x
  have hleft (u v : Bool) :
      (fun i => extendBits (Sum.inl a : I ⊕ J) (Sum.inl b) (fun h => hab (Sum.inl.inj h)) x u v (Sum.inl i)) =
        extendBits a b hab (fun p => x (remainingTensorLeft a b (.inl p))) u v := by
    funext i
    by_cases ha : i=a
    · subst i; simp [extendBits,splitPorts]
    by_cases hb : i=b
    · subst i; simp [extendBits,splitPorts,Ne.symm hab]
    simp [extendBits,splitPorts,ha,hb,remainingTensorLeft]
  have hright (u v : Bool) :
      (fun j => extendBits (Sum.inl a : I ⊕ J) (Sum.inl b) (fun h => hab (Sum.inl.inj h)) x u v (Sum.inr j)) =
        fun j => x (remainingTensorLeft a b (.inr j)) := by
    funext j
    simp [extendBits,splitPorts,remainingTensorLeft]
  rw [card_four]
  simp only [Tensor.reindex_apply,Tensor.tensor_apply,hleft,hright]
  rw [card_four]
  ring

def exposedRemaining : I ≃ Remaining (Sum.inr false : I ⊕ Bool) (Sum.inr true) where
  toFun i := ⟨.inl i,by simp⟩
  invFun := by
    rintro ⟨i,hi⟩
    cases i with
    | inl i => exact i
    | inr b => cases b with
      | false => exact False.elim (hi.1 rfl)
      | true => exact False.elim (hi.2 rfl)
  left_inv i := rfl
  right_inv p := by
    rcases p with ⟨i,hi⟩
    cases i with
    | inl i => rfl
    | inr b => cases b with
      | false => exact False.elim (hi.1 rfl)
      | true => exact False.elim (hi.2 rfl)

omit [Fintype I] in
theorem card_exposed (E : Kernel AlgebraicComplex)
    (f : Tensor AlgebraicComplex (I ⊕ Bool)) :
    card E (.inr false) (.inr true) (by simp) f =
      Tensor.reindex exposedRemaining (contractKernel E f) := by
  funext x
  unfold card contractKernel
  simp only [Tensor.reindex_apply]
  apply Finset.sum_congr rfl
  intro v _
  congr 2
  funext i
  cases i with
  | inl i => simp [splitPorts,exposedRemaining]
  | inr b => cases b <;> simp [splitPorts]

theorem phaseProduct_reindex_iff {N : ℕ} (e : I ≃ J) (f : Tensor AlgebraicComplex I) :
    PhaseProduct N (Tensor.reindex e f) ↔ PhaseProduct N f := by
  constructor
  · intro h
    simpa only [Tensor.reindex_symm] using h.reindex e.symm
  · exact fun h => h.reindex e

theorem card_membership_reindex {N : ℕ} (E : Kernel AlgebraicComplex) (e : I ≃ J)
    (a b : I) (hab : a ≠ b) (f : Tensor AlgebraicComplex I) :
    PhaseProduct N (card E (e a) (e b) (e.injective.ne hab) (Tensor.reindex e f)) ↔
      PhaseProduct N (card E a b hab f) := by
  rw [card_reindex]
  exact phaseProduct_reindex_iff _ _

theorem card_membership_ports {N : ℕ} (E : Kernel AlgebraicComplex)
    (f : Tensor AlgebraicComplex I) {a b a' b' : I} (hab : a≠b) (hab' : a'≠b')
    (ha : a=a') (hb : b=b') :
    PhaseProduct N (card E a b hab f) ↔ PhaseProduct N (card E a' b' hab' f) := by
  subst a'
  subst b'
  rfl

theorem card_scale (E : Kernel AlgebraicComplex) (a b : I) (hab : a ≠ b)
    (c : AlgebraicComplex) (f : Tensor AlgebraicComplex I) :
    card E a b hab (c • f) = c • card E a b hab f := by
  unfold card
  have hr : Tensor.reindex (splitPorts a b hab) (c • f) =
      c • Tensor.reindex (splitPorts a b hab) f := rfl
  rw [hr,contractKernel_scale_tensor]

theorem card_kernel_scale (E : Kernel AlgebraicComplex) (a b : I) (hab : a ≠ b)
    (c : AlgebraicComplex) (f : Tensor AlgebraicComplex I) :
    card (c • E) a b hab f = c • card E a b hab f := by
  funext x
  unfold card contractKernel
  simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem card_zero (E : Kernel AlgebraicComplex) (a b : I) (hab : a ≠ b) :
    card E a b hab (0 : Tensor AlgebraicComplex I) = 0 := by
  funext x
  simp [card,contractKernel,Tensor.reindex]

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductClosure
