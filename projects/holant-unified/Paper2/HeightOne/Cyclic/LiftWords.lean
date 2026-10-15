import Paper2.HeightOne.Cyclic.MatchingDeck

/-! Literal zero-slice and residual-port identities for weight-two words. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open EndpointSelfLoop
variable {K : Type*} [Field K] {ι : Type} [Fintype ι]

lemma extendBits_pairWord (a b : ι) (hab : a ≠ b) (u v : Remaining a b) :
    extendBits a b hab (pairWord u v) false false = pairWord u.val v.val := by
  classical
  funext i
  by_cases ha : i = a
  · subst i
    simp [extendBits, splitPorts, pairWord, Ne.symm u.property.1, Ne.symm v.property.1]
  · by_cases hb : i = b
    · subst i
      simp [extendBits, splitPorts, pairWord, Ne.symm u.property.2, Ne.symm v.property.2, ha]
    · simp only [extendBits, splitPorts, dif_neg ha, dif_neg hb, Equiv.coe_fn_mk, Sum.elim_inl, pairWord]
      congr 1
      exact propext (or_congr Subtype.ext_iff Subtype.ext_iff)

lemma pairWord_pullback (a b : ι)
    (p q : Fin (Fintype.card (Remaining a b))) :
    (fun i => weightTwoWord p q ((Fintype.equivFin (Remaining a b)) i)) =
      pairWord ((Fintype.equivFin (Remaining a b)).symm p)
        ((Fintype.equivFin (Remaining a b)).symm q) := by
  classical
  funext i
  simp only [weightTwoWord, pairWord, Equiv.apply_eq_iff_eq_symm_apply]

lemma zero_slice_weightTwo (f : Tensor K ι)
    (hW : ∀ u v, u ≠ v → f (pairWord u v) = 0)
    (a b : ι) (hab : a ≠ b)
    (p q : Fin (Fintype.card (Remaining a b))) (hpq : p ≠ q) :
    Tensor.reindex (Fintype.equivFin (Remaining a b))
      (fun x => f (extendBits a b hab x false false)) (weightTwoWord p q) = 0 := by
  change f (extendBits a b hab (fun i => weightTwoWord p q ((Fintype.equivFin (Remaining a b)) i)) false false) = 0
  rw [pairWord_pullback, extendBits_pairWord]
  apply hW
  intro h
  exact hpq ((Fintype.equivFin (Remaining a b)).symm.injective (Subtype.ext h))

end
end Paper2.HeightOne.Cyclic
