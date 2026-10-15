import Paper2.PrimeFactorization
import Paper2.TensorAction
import Mathlib.Tactic

/-! Actual positive-arity cuts of a finite binary decomposition. This is a
literal ordered tensor-factor witness, not a rank or factorization assumption. -/
namespace Paper2.HeightOne
open Tractable
open scoped BigOperators
noncomputable section

private def splitFirstPair (r : ℕ) :
    (Fin 2 ⊕ (Fin r × Fin 2)) ≃ (Fin (r+1) × Fin 2) where
  toFun
    | .inl j => (0,j)
    | .inr (i,j) => (i.succ,j)
  invFun p := Fin.cases (.inl p.2) (fun i => .inr (i,p.2)) p.1
  left_inv := by rintro (j | ⟨i,j⟩) <;> simp
  right_inv := by
    rintro ⟨i,j⟩
    induction i using Fin.cases with
    | zero => rfl
    | succ i => rfl

/-- Two or more binary blocks produce a genuine nontrivial ordered cut. -/
theorem binary_decomposition_not_tensorPrime {n : ℕ}
    (D : TensorDecomposition AlgebraicComplex n) (htwo : ∀ i, D.arity i = 2)
    (hn : 2 < n) : ¬ TensorPrime D.value := by
  rcases D with ⟨count,arity,factor,ports,scale⟩
  change ∀ i, arity i = 2 at htwo
  have he : arity = fun _ => 2 := funext htwo
  subst arity
  have hc : count * 2 = n := by simpa using Fintype.card_congr ports
  cases count with
  | zero => omega
  | succ r =>
    have hr : 0 < r * 2 := by omega
    let ep : (Fin (r+1) × Fin 2) ≃ Fin n :=
      (Equiv.sigmaEquivProd (Fin (r+1)) (Fin 2)).symm.trans ports
    let e : Fin (2 + r*2) ≃ Fin n :=
      ((finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl (Fin 2))
        (finProdFinEquiv : Fin r × Fin 2 ≃ Fin (r*2)).symm)).trans
        (splitFirstPair r)).trans ep
    let a : Signature AlgebraicComplex 2 := fun x => (scale : AlgebraicComplex) * factor 0 x
    let b : Signature AlgebraicComplex (r*2) := fun x =>
      ∏ i : Fin r, factor i.succ (fun j => x (finProdFinEquiv (i,j)))
    intro hp
    apply hp.2 2 (r*2) (by decide) hr e a b
    funext x
    change ((scale : AlgebraicComplex) * factor 0 (fun j => x (e (Fin.castAdd (r*2) j)))) *
        (∏ i : Fin r, factor i.succ (fun j => x (e (Fin.natAdd 2 (finProdFinEquiv (i,j)))))) =
      (scale : AlgebraicComplex) * ∏ i : Fin (r+1), factor i (fun j => x (ports ⟨i,j⟩))
    rw [Fin.prod_univ_succ]
    simp only [e,Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd,Equiv.sumCongr_apply,Equiv.refl_apply,
      Sum.map_inl,Sum.map_inr,Equiv.symm_apply_apply,splitFirstPair,Equiv.coe_fn_mk,
      ep,Equiv.sigmaEquivProd_symm_apply,mul_assoc]


lemma coordinateAction_reindex {m n : ℕ} (M : Kernel AlgebraicComplex)
    (e : Fin m ≃ Fin n) (f : Signature AlgebraicComplex m) :
    Signature.coordinateAction (fun _ => M) (Tensor.reindex e f) =
      Tensor.reindex e (Signature.coordinateAction (fun _ => M) f) := by
  classical
  funext x
  unfold Signature.coordinateAction Tensor.reindex
  apply Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Bool))
  intro y
  congr 1
  exact (e.prod_comp (fun k => M (x k) (y k))).symm

lemma coordinateAction_tensor {m n : ℕ} (M : Kernel AlgebraicComplex)
    (a : Signature AlgebraicComplex m) (b : Signature AlgebraicComplex n) :
    Signature.coordinateAction (fun _ => M) (Signature.tensor a b) =
      Signature.tensor (Signature.coordinateAction (fun _ => M) a)
        (Signature.coordinateAction (fun _ => M) b) := by
  classical
  funext x
  let e : (Fin (m+n) → Bool) ≃ ((Fin m → Bool) × (Fin n → Bool)) :=
    (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) Bool)
  calc
    _ = ∑ p : (Fin m → Bool) × (Fin n → Bool),
      ((∏ i, M (x (Fin.castAdd n i)) (p.1 i)) * a p.1) *
        ((∏ j, M (x (Fin.natAdd m j)) (p.2 j)) * b p.2) := by
      unfold Signature.coordinateAction
      apply Fintype.sum_equiv e
      intro y
      simp only [Signature.tensor_apply, e, Equiv.trans_apply, Equiv.arrowCongr_apply,
        Equiv.sumArrowEquivProdArrow_apply_fst,Equiv.sumArrowEquivProdArrow_apply_snd,
        Equiv.refl_apply, Equiv.symm_symm,finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right,Fin.prod_univ_add]
      change ((∏ i, M (x (Fin.castAdd n i)) (y (Fin.castAdd n i))) *
        (∏ j, M (x (Fin.natAdd m j)) (y (Fin.natAdd m j)))) *
        (a (fun i => y (Fin.castAdd n i)) * b (fun j => y (Fin.natAdd m j))) =
        ((∏ i, M (x (Fin.castAdd n i)) (y (Fin.castAdd n i))) * a (fun i => y (Fin.castAdd n i))) *
        ((∏ j, M (x (Fin.natAdd m j)) (y (Fin.natAdd m j))) * b (fun j => y (Fin.natAdd m j)))
      ring
    _ = _ := by
      simp only [Fintype.sum_prod_type,Signature.tensor_apply,Signature.coordinateAction,
        Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm

/-- A single invertible coordinate action preserves the literal tensor-prime
property, with the same ordered bipartition and inverse actions on its factors. -/
theorem tensorPrime_action {n : ℕ} (B : InvertibleKernel)
    {f : Signature AlgebraicComplex n} (hf : TensorPrime f) : TensorPrime (B.action f) := by
  refine ⟨?_,?_⟩
  · intro hz
    apply hf.1
    have he := congrArg B.symm.action hz
    rw [B.symm_action_action] at he
    simpa only [InvertibleKernel.action,Signature.coordinateAction_zero] using he
  · intro m k hm hk e a b he
    apply hf.2 m k hm hk e (B.symm.action a) (B.symm.action b)
    have hi := congrArg B.symm.action he
    rw [B.symm_action_action] at hi
    change Signature.coordinateAction (fun _ => B.inverse)
      (Tensor.reindex e (Signature.tensor a b)) = f at hi
    rw [coordinateAction_reindex,coordinateAction_tensor] at hi
    exact hi

theorem tensorPrime_action_iff {n : ℕ} (B : InvertibleKernel)
    (f : Signature AlgebraicComplex n) : TensorPrime (B.action f) ↔ TensorPrime f := by
  refine ⟨fun h => ?_,tensorPrime_action B⟩
  simpa using tensorPrime_action B.symm h

end
end Paper2.HeightOne


