import Paper2.SourceFaithful.SourceStatements.PhaseProductBlockCards
import Paper2.SourceFaithful.SourceStatements.PhaseProductRawPrimeAssembly
import Paper2.HeightOne.PhaseCards.OrientedCards

/-! Source Lemma 5.11: literal phase-product closure under an arbitrary
ordered two-port contraction. The proof treats the actual partition, retaining
every other block, the full scalar, and possible zero or nullary output. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductClosure
noncomputable section
open Paper2 Tractable HeightOne.PhaseCards EndpointSelfLoop
open PhaseProductDecomposition
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 10000
attribute [local instance] Classical.propDecidable

theorem decomposition_card {N n : ℕ} {E : Kernel AlgebraicComplex} (rule : LocalRule N E)
    (D : TensorDecomposition AlgebraicComplex n) (hD : ∀ i, EvenPhaseBlock N (D.factor i))
    (a b : Fin n) (hab : a≠b) : PhaseProduct N (card E a b hab D.value) := by
  obtain ⟨i,ia,ha⟩ : ∃ (i : Fin D.count) (ia : Fin (D.arity i)), D.ports ⟨i,ia⟩=a :=
    ⟨(D.ports.symm a).1,(D.ports.symm a).2,D.ports.apply_symm_apply a⟩
  obtain ⟨j,jb,hb⟩ : ∃ (j : Fin D.count) (jb : Fin (D.arity j)), D.ports ⟨j,jb⟩=b :=
    ⟨(D.ports.symm b).1,(D.ports.symm b).2,D.ports.apply_symm_apply b⟩
  by_cases hij : i=j
  · subst j
    have hlocal : ia≠jb := by
      intro he
      apply hab
      rw [← ha,← hb,he]
    have hrem := remainder_phaseProduct D i (fun j => PhaseProduct.of_block (hD j))
    have hcard : PhaseProduct N (card E (Sum.inl ia) (Sum.inl jb)
        (fun he => hlocal (Sum.inl.inj he)) (Tensor.tensor (D.factor i) (remainder D i))) := by
      rw [card_tensor_left]
      exact ((block_card rule _ (hD i) ia jb hlocal).tensor hrem).reindex _
    have ht := (card_membership_reindex E (peelPorts D i) (Sum.inl ia) (Sum.inl jb)
      (fun he => hlocal (Sum.inl.inj he)) (Tensor.tensor (D.factor i) (remainder D i))).mpr hcard
    rw [peel_value] at ht
    exact (card_membership_ports E D.value _ hab
      ((peelPorts_left D i ia).trans ha) ((peelPorts_left D i jb).trans hb)).mp ht
  · have hlocal : (Sum.inl ia : Fin (D.arity i) ⊕ Fin (D.arity j))≠Sum.inr jb := by simp
    have hrem := remainderTwo_phaseProduct D i j (fun k => PhaseProduct.of_block (hD k))
    have hcard : PhaseProduct N (card E (Sum.inl (Sum.inl ia)) (Sum.inl (Sum.inr jb))
        (fun he => hlocal (Sum.inl.inj he))
        (Tensor.tensor (Tensor.tensor (D.factor i) (D.factor j)) (remainderTwo D i j))) := by
      rw [card_tensor_left]
      exact ((two_block_card rule _ _ (hD i) (hD j) ia jb).tensor hrem).reindex _
    have ht := (card_membership_reindex E (peelTwoPorts D i j hij)
      (Sum.inl (Sum.inl ia)) (Sum.inl (Sum.inr jb))
      (fun he => hlocal (Sum.inl.inj he))
      (Tensor.tensor (Tensor.tensor (D.factor i) (D.factor j)) (remainderTwo D i j))).mpr hcard
    rw [peel_two_value] at ht
    exact (card_membership_ports E D.value _ hab
      ((peelTwoPorts_first D i j hij ia).trans ha)
      ((peelTwoPorts_second D i j hij jb).trans hb)).mp ht

theorem phaseProduct_card {I : Type} [Fintype I] {N : ℕ} {E : Kernel AlgebraicComplex}
    (rule : LocalRule N E) {f : Tensor AlgebraicComplex I} (hf : PhaseProduct N f)
    (a b : I) (hab : a≠b) : PhaseProduct N (card E a b hab f) := by
  rcases hf with hz | ⟨n,D,e,hD,he⟩
  · rw [hz,card_zero]
    exact PhaseProduct.zero N _
  · have hab' : e.symm a≠e.symm b := e.symm.injective.ne hab
    have ht := (card_membership_reindex E e (e.symm a) (e.symm b) hab' D.value).mpr
      (decomposition_card rule D hD _ _ hab')
    rw [he] at ht
    exact (card_membership_ports E f _ hab (e.apply_symm_apply a) (e.apply_symm_apply b)).mp ht

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductClosure

namespace Paper2.HeightOne.PhaseCards
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Paper2 Tractable SourceFaithful.SourceStatements.PhaseProductClosure
variable {I : Type} [Fintype I] {N : ℕ} {f : Tensor AlgebraicComplex I}

/-- Arbitrary two named ports, including contractions across distinct blocks. -/
theorem PhaseProduct.card_plus (hf : PhaseProduct N f) (s : rootsOfUnity N AlgebraicComplex)
    (a b : I) (hab : a≠b) : PhaseProduct N (card (plusKernel s.val) a b hab f) :=
  phaseProduct_card (plus_rule s) hf a b hab

theorem PhaseProduct.card_minus (hf : PhaseProduct N f) (s : rootsOfUnity N AlgebraicComplex)
    (a b : I) (hab : a≠b) : PhaseProduct N (card (minusKernel s.val) a b hab f) :=
  phaseProduct_card (minus_rule s) hf a b hab

theorem PhaseProduct.card_minus_transpose (hf : PhaseProduct N f)
    (s : rootsOfUnity N AlgebraicComplex) (a b : I) (hab : a≠b) :
    PhaseProduct N (card (minusKernel s.val).transpose a b hab f) := by
  rw [minusKernel_transpose _ (Units.ne_zero s.val),card_kernel_scale]
  simpa only [Subgroup.coe_inv,Units.val_inv_eq_inv_val] using
    (hf.card_minus s⁻¹ a b hab).scale (-(s.val : AlgebraicComplex))

theorem PhaseProduct.card_plus_transpose (hf : PhaseProduct N f)
    (s : rootsOfUnity N AlgebraicComplex) (a b : I) (hab : a≠b) :
    PhaseProduct N (card (plusKernel s.val).transpose a b hab f) := by
  have he : (plusKernel s.val).transpose=plusKernel s.val := by
    funext x y; cases x <;> cases y <;> rfl
  rw [he]
  exact hf.card_plus s a b hab

theorem PhaseProduct.card_xor (hf : PhaseProduct N f) (s : rootsOfUnity N AlgebraicComplex)
    (a b : I) (hab : a≠b) (u v : Bool) :
    PhaseProduct N (card (xorKernel u v s.val) a b hab f) := by
  have forward (v : Bool) (s : rootsOfUnity N AlgebraicComplex) :
      PhaseProduct N (card (xorKernel false v s.val) a b hab f) := by
    cases v
    · rw [xorKernel_false_false]; exact hf.card_plus s a b hab
    · rw [xorKernel_false_true]; exact hf.card_minus s a b hab
  cases u
  · exact forward v s
  · rw [xorKernel_reverse _ _ (Units.ne_zero s.val),card_kernel_scale]
    simpa only [Subgroup.coe_inv,Units.val_inv_eq_inv_val] using
      (forward (!v) s⁻¹).scale (-(s.val : AlgebraicComplex))

theorem PhaseProduct.contract_plus {J : Type} [Fintype J]
    {g : Tensor AlgebraicComplex (J ⊕ Bool)} (hg : PhaseProduct N g)
    (s : rootsOfUnity N AlgebraicComplex) :
    PhaseProduct N (contractKernel (plusKernel s.val) g) := by
  apply (phaseProduct_reindex_iff exposedRemaining _).mp
  rw [← card_exposed]
  exact hg.card_plus s (.inr false) (.inr true) (by simp)

theorem PhaseProduct.contract_minus {J : Type} [Fintype J]
    {g : Tensor AlgebraicComplex (J ⊕ Bool)} (hg : PhaseProduct N g)
    (s : rootsOfUnity N AlgebraicComplex) :
    PhaseProduct N (contractKernel (minusKernel s.val) g) := by
  apply (phaseProduct_reindex_iff exposedRemaining _).mp
  rw [← card_exposed]
  exact hg.card_minus s (.inr false) (.inr true) (by simp)

theorem PhaseProduct.card_scaled_xor (hf : PhaseProduct N f)
    (s : rootsOfUnity N AlgebraicComplex) (a b : I) (hab : a≠b)
    (u v : Bool) (c : AlgebraicComplex) :
    PhaseProduct N (card (c • xorKernel u v s.val) a b hab f) := by
  rw [card_kernel_scale]
  exact (hf.card_xor s a b hab u v).scale c

end
end Paper2.HeightOne.PhaseCards

namespace Paper2.SourceFaithful.SourceStatements
noncomputable section
open Paper2 Tractable HeightOne.PhaseCards PhaseProductDecomposition
set_option backward.isDefEq.respectTransparency false

/-- The literal contraction clauses of source Lemma 5.11 on an arbitrary
finite original port type and every ordered pair of distinct occurrences. -/
theorem source_5_11 {I : Type} [Fintype I] {N : ℕ} (f : Tensor AlgebraicComplex I)
    (hf : PhaseProduct N f) (s : rootsOfUnity N AlgebraicComplex)
    (a b : I) (hab : a≠b) :
    PhaseProduct N (card (plusKernel s.val) a b hab f) ∧
    PhaseProduct N (card (minusKernel s.val) a b hab f) ∧
    PhaseProduct N (card (plusKernel s.val).transpose a b hab f) ∧
    PhaseProduct N (card (minusKernel s.val).transpose a b hab f) :=
  ⟨hf.card_plus s a b hab,hf.card_minus s a b hab,
    hf.card_plus_transpose s a b hab,hf.card_minus_transpose s a b hab⟩

/-- Prime-factor membership is converted to whole-tensor membership before
contracting. Empty and zero tensors and every nullary scalar are retained. -/
theorem source_5_11_prime_factors {I : Type} [Fintype I] {N : ℕ}
    (f : Tensor AlgebraicComplex I) (hf : PositivePrimeFactorsPhaseProduct (N:=N) f)
    (s : rootsOfUnity N AlgebraicComplex) (a b : I) (hab : a≠b) (u v : Bool) :
    PhaseProduct N (card (xorKernel u v s.val) a b hab f) :=
  (phaseProduct_of_raw_prime_factors f hf).card_xor s a b hab u v

end
end Paper2.SourceFaithful.SourceStatements

