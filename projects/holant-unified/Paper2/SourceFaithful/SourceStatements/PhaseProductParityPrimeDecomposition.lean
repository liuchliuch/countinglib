import Paper2.SourceFaithful.SourceStatements.PhaseProductDecomposition
import Paper2.HeightOne.TensorPrimeTools

/-! Positive actual decompositions of a tensor-prime tensor have one factor.
The proof retains the original scalar and the literal ordered port map. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable HeightOne PhaseProductDecomposition
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Any second positive factor gives a genuine positive ordered tensor cut. -/
theorem prime_count_one {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (hn : 0 < n) (hp : TensorPrime D.value) (hpos : ∀ i, 0 < D.arity i) :
    D.count = 1 := by
  classical
  have hc : 0 < D.count := by
    have hh := (D.ports.symm ⟨0,hn⟩).1.isLt
    omega
  by_contra hcount
  have hc2 : 2 ≤ D.count := by omega
  let i : Fin D.count := ⟨0,hc⟩
  let j : Fin D.count := ⟨1,hc2⟩
  have hji : j ≠ i := by
    intro he
    have hh := congrArg Fin.val he
    change 1 = 0 at hh
    omega
  have hk : 0 < Fintype.card (OtherPorts D i) :=
    Fintype.card_pos_iff.mpr ⟨⟨⟨j,hji⟩,⟨0,hpos j⟩⟩⟩
  let r := Fintype.equivFin (OtherPorts D i)
  let e : Fin (D.arity i + Fintype.card (OtherPorts D i)) ≃ Fin n :=
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr (Equiv.refl (Fin (D.arity i))) r.symm)).trans (peelPorts D i)
  let b : Signature AlgebraicComplex (Fintype.card (OtherPorts D i)) :=
    Tensor.reindex r (remainder D i)
  apply hp.2 (D.arity i) (Fintype.card (OtherPorts D i)) (hpos i) hk e (D.factor i) b
  calc
    Tensor.reindex e (Signature.tensor (D.factor i) b) =
        Tensor.reindex (peelPorts D i) (Tensor.tensor (D.factor i) (remainder D i)) := by
      funext x
      simp only [Tensor.reindex_apply,Signature.tensor_apply,Tensor.tensor_apply,b,e,
        Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,
        finSumFinEquiv_symm_apply_natAdd,Equiv.sumCongr_apply,
        Equiv.refl_apply,Sum.map_inl,Sum.map_inr,Equiv.symm_apply_apply]
    _ = D.value := peel_value D i

/-- Its literal ordered ports form the actual factor-to-output equivalence. -/
def singlePorts {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (hc : D.count = 1) (i : Fin D.count) : Fin (D.arity i) ≃ Fin n := by
  classical
  haveI : Subsingleton (Fin D.count) := by rw [hc]; infer_instance
  exact Equiv.ofBijective (fun k => D.ports ⟨i,k⟩) (by
    constructor
    · intro a b h
      have hh := D.ports.injective h
      exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2
    · intro a
      rcases h : D.ports.symm a with ⟨j,k⟩
      have hj : j = i := Subsingleton.elim _ _
      subst j
      exact ⟨k,by simpa only [h] using D.ports.apply_symm_apply a⟩)

@[simp] theorem singlePorts_apply {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (hc : D.count = 1) (i : Fin D.count) (k : Fin (D.arity i)) :
    singlePorts D hc i k = D.ports ⟨i,k⟩ := rfl

/-- The sole actual factor has the same arity as the complete tensor. -/
theorem single_arity {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (hc : D.count = 1) (i : Fin D.count) : D.arity i = n := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (singlePorts D hc i)

/-- Every scalar and every ordered factor port is retained in reconstruction. -/
theorem single_value {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (hc : D.count = 1) (i : Fin D.count) :
    D.value = (D.scale : AlgebraicComplex) • Tensor.reindex (singlePorts D hc i) (D.factor i) := by
  classical
  have : Subsingleton (Fin D.count) := by rw [hc]; infer_instance
  funext x
  simp only [TensorDecomposition.value,Pi.smul_apply,smul_eq_mul,
    Tensor.reindex_apply,singlePorts_apply]
  congr 1
  apply Finset.prod_eq_single i
  · intro j _ hji
    exact False.elim (hji (Subsingleton.elim _ _))
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity

