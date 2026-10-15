import Paper2.HeightOne.TensorPrimeTools

/-! Independent invertible actions on named ports preserve literal tensor
primality.  This applies to actual binary dressing without pretending that
its distinct port matrices are a single global holographic basis.
-/
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable
open scoped BigOperators

lemma coordinateAction_reindex_ports {m n : ℕ}
    (A : Fin n → Kernel AlgebraicComplex) (e : Fin m ≃ Fin n)
    (f : Signature AlgebraicComplex m) :
    Signature.coordinateAction A (Tensor.reindex e f) =
      Tensor.reindex e (Signature.coordinateAction (fun i => A (e i)) f) := by
  classical
  funext x
  unfold Signature.coordinateAction Tensor.reindex
  apply Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Bool))
  intro y
  congr 1
  exact (e.prod_comp (fun k => A k (x k) (y k))).symm

lemma coordinateAction_tensor_ports {m n : ℕ}
    (A : Fin (m + n) → Kernel AlgebraicComplex)
    (a : Signature AlgebraicComplex m) (b : Signature AlgebraicComplex n) :
    Signature.coordinateAction A (Signature.tensor a b) =
      Signature.tensor
        (Signature.coordinateAction (fun i => A (Fin.castAdd n i)) a)
        (Signature.coordinateAction (fun i => A (Fin.natAdd m i)) b) := by
  classical
  funext x
  let e : (Fin (m+n) → Bool) ≃ ((Fin m → Bool) × (Fin n → Bool)) :=
    (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) Bool)
  calc
    _ = ∑ p : (Fin m → Bool) × (Fin n → Bool),
      ((∏ i, A (Fin.castAdd n i) (x (Fin.castAdd n i)) (p.1 i)) * a p.1) *
        ((∏ j, A (Fin.natAdd m j) (x (Fin.natAdd m j)) (p.2 j)) * b p.2) := by
      unfold Signature.coordinateAction
      apply Fintype.sum_equiv e
      intro y
      simp only [Signature.tensor_apply, e, Equiv.trans_apply, Equiv.arrowCongr_apply,
        Equiv.sumArrowEquivProdArrow_apply_fst, Equiv.sumArrowEquivProdArrow_apply_snd,
        Equiv.refl_apply, Equiv.symm_symm, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Fin.prod_univ_add]
      change ((∏ i, A (Fin.castAdd n i) (x (Fin.castAdd n i)) (y (Fin.castAdd n i))) *
        (∏ j, A (Fin.natAdd m j) (x (Fin.natAdd m j)) (y (Fin.natAdd m j)))) *
        (a (fun i => y (Fin.castAdd n i)) * b (fun j => y (Fin.natAdd m j))) =
        ((∏ i, A (Fin.castAdd n i) (x (Fin.castAdd n i)) (y (Fin.castAdd n i))) * a (fun i => y (Fin.castAdd n i))) *
        ((∏ j, A (Fin.natAdd m j) (x (Fin.natAdd m j)) (y (Fin.natAdd m j))) * b (fun j => y (Fin.natAdd m j)))
      ring
    _ = _ := by
      simp only [Fintype.sum_prod_type, Signature.tensor_apply, Signature.coordinateAction,
        Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

/-- Only the displayed inverse equation is used.  A different inverse may
serve each port, and every actual ordered tensor cut is retained. -/
theorem tensorPrime_coordinateAction_ports {n : ℕ}
    (A B : Fin n → Kernel AlgebraicComplex)
    (hBA : ∀ i, Kernel.mul (B i) (A i) = Signature.equality)
    {f : Signature AlgebraicComplex n} (hf : TensorPrime f) :
    TensorPrime (Signature.coordinateAction A f) := by
  have hcancel := Signature.coordinateAction_cancel B A hBA f
  refine ⟨?_, ?_⟩
  · intro hz
    apply hf.1
    have he := congrArg (Signature.coordinateAction B) hz
    rw [hcancel, Signature.coordinateAction_zero] at he
    exact he
  · intro m k hm hk e a b he
    apply hf.2 m k hm hk e
      (Signature.coordinateAction (fun i => B (e (Fin.castAdd k i))) a)
      (Signature.coordinateAction (fun i => B (e (Fin.natAdd m i))) b)
    have hi := congrArg (Signature.coordinateAction B) he
    rw [hcancel] at hi
    rw [coordinateAction_reindex_ports, coordinateAction_tensor_ports] at hi
    exact hi

end
end Paper2.HeightOne.Cyclic
