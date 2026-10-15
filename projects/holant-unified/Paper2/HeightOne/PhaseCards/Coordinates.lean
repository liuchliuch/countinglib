import Paper2.HeightOne.PhaseCards.Kernels
import Paper2.HeightOne.Parity

/-! Finite-sum Walsh coordinate transport across a literal two-port contraction.
Every equality is analytic; no linear combination is asserted to be a gadget. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.PhaseCards
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {K ι κ : Type*} [CommSemiring K] [Fintype ι] [Fintype κ]

/-- Uniform coordinate action on any finite ordered port type. -/
def action (M : Kernel K) (f : Tensor K ι) : Tensor K ι := by
  classical
  exact fun x => ∑ y : ι → Bool, (∏ i, M (x i) (y i)) * f y

lemma action_comp (M N : Kernel K) (f : Tensor K ι) :
    action M (action N f) = action (Kernel.mul M N) f := by
  classical
  funext x
  simp only [action, Kernel.mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Fintype.prod_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.prod_mul_distrib, mul_assoc]

lemma action_one (f : Tensor K ι) : action Signature.equality f = f := by
  classical
  funext x
  have hprod (y : ι → Bool) : (∏ i, Signature.equality (K := K) (x i) (y i)) =
      if x = y then 1 else 0 := by
    simp only [Signature.equality, Fintype.prod_boole, ← funext_iff]
  simp [action, hprod]

lemma action_cancel (M N : Kernel K) (hMN : Kernel.mul M N = Signature.equality)
    (f : Tensor K ι) : action M (action N f) = f := by
  rw [action_comp, hMN, action_one]

lemma action_reindex (M : Kernel K) (e : ι ≃ κ) (f : Tensor K ι) :
    action M (Tensor.reindex e f) = Tensor.reindex e (action M f) := by
  classical
  funext x
  unfold action Tensor.reindex
  apply Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Bool))
  intro y
  congr 1
  exact (e.prod_comp (fun k => M (x k) (y k))).symm

/-- All assignments to the two exposed ports are retained, including zeros. -/
def contractKernel (E : Kernel K) (f : Tensor K (ι ⊕ Bool)) : Tensor K ι := by
  classical
  exact fun x => ∑ v : Bool → Bool, E (v false) (v true) * f (Sum.elim x v)

lemma action_pair (M : Kernel K) (f : Tensor K (ι ⊕ Bool))
    (x : ι → Bool) (v : Bool → Bool) :
    action M f (Sum.elim x v) =
      ∑ y : ι → Bool, ∑ w : Bool → Bool,
        ((∏ i, M (x i) (y i)) * (∏ b : Bool, M (v b) (w b))) * f (Sum.elim y w) := by
  classical
  letI : DecidableEq (ι ⊕ Bool) := fun _ _ => Classical.propDecidable _
  unfold action
  calc
    _ = ∑ p : (ι → Bool) × (Bool → Bool),
        ((∏ i, M (x i) (p.1 i)) * (∏ b : Bool, M (v b) (p.2 b))) *
          f (Sum.elim p.1 p.2) := by
      apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow ι Bool Bool)
      intro y
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
        Equiv.sumArrowEquivProdArrow_apply_fst, Equiv.sumArrowEquivProdArrow_apply_snd]
      congr 1
      congr 1
      funext i
      cases i <;> rfl
    _ = _ := Fintype.sum_prod_type _

lemma sum_bilinear (E M : Kernel K) (w : Bool → Bool) :
    (∑ v : Bool → Bool, E (v false) (v true) * ∏ b : Bool, M (v b) (w b)) =
      Kernel.pullback E M (w false) (w true) := by
  classical
  calc
    _ = ∑ p : Bool × Bool, E p.1 p.2 *
        (M p.1 (w false) * M p.2 (w true)) := by
      apply Fintype.sum_equiv (Equiv.boolArrowEquivProd Bool)
      intro v
      simp [Fintype.prod_bool, mul_comm]
    _ = _ := by
      simp [Kernel.pullback, Kernel.mul_apply, Kernel.transpose, Fintype.sum_prod_type]
      ring

/-- Moving coordinate actions across the deleted pair pulls the physical
kernel back by Mᵀ E M, retaining the action on every surviving port. -/
theorem contractKernel_action (E M : Kernel K) (f : Tensor K (ι ⊕ Bool)) :
    contractKernel E (action M f) = action M (contractKernel (Kernel.pullback E M) f) := by
  classical
  funext x
  simp only [contractKernel, action_pair, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold action
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]
  simp only [contractKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  have he := sum_bilinear E M w
  calc
    _ = ((∏ i, M (x i) (y i)) * f (Sum.elim y w)) *
        (∑ v : Bool → Bool, E (v false) (v true) * ∏ b : Bool, M (v b) (w b)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = _ := by rw [he]; ring

end
end Paper2.HeightOne.PhaseCards
