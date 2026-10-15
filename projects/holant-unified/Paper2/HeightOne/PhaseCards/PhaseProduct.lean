import Paper2.HeightOne.PhaseCards.BlockContraction
import Paper2.PrimeFactorization

/-! The source's P_N class: a literal finite tensor product of nonempty even
complementary two-point blocks, with their prescribed ratio cosets. It is not
defined as a contraction closure or as the standard product class P. -/
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable

/-- One nonempty even block, with an explicit half-size and offset. -/
def EvenPhaseBlock (N : ℕ) {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  ∃ (k : ℕ) (a : Fin n → Bool) (r : AlgebraicComplex),
    n = 2 * (k + 1) ∧ PhaseRatio N (k + 1) r ∧ f = twoPoint a r

/-- A literal even-block partition is supplied by D.ports; its global scalar
is the nonzero unit D.scale. Zero is included separately, as in the source. -/
def PhaseProduct (N : ℕ) {ι : Type} (f : Tensor AlgebraicComplex ι) : Prop :=
  f = 0 ∨ ∃ (n : ℕ) (D : TensorDecomposition AlgebraicComplex n) (e : Fin n ≃ ι),
    (∀ i, EvenPhaseBlock N (D.factor i)) ∧ Tensor.reindex e D.value = f

lemma PhaseProduct.zero (N : ℕ) (ι : Type) : PhaseProduct N (0 : Tensor AlgebraicComplex ι) :=
  Or.inl rfl

lemma PhaseProduct.of_block {N n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : EvenPhaseBlock N f) : PhaseProduct N f := by
  exact Or.inr ⟨n, TensorDecomposition.singleton f, Equiv.refl _, fun _ => hf, by simp⟩

lemma PhaseProduct.reindex {N : ℕ} {ι κ : Type} {f : Tensor AlgebraicComplex ι}
    (hf : PhaseProduct N f) (e : ι ≃ κ) : PhaseProduct N (Tensor.reindex e f) := by
  rcases hf with rfl | ⟨n, D, p, hD, rfl⟩
  · left; rfl
  · exact Or.inr ⟨n, D, p.trans e, hD, rfl⟩

lemma PhaseProduct.scale {N : ℕ} {ι : Type} {f : Tensor AlgebraicComplex ι}
    (hf : PhaseProduct N f) (c : AlgebraicComplex) : PhaseProduct N (c • f) := by
  by_cases hc : c = 0
  · subst c; simpa using PhaseProduct.zero N ι
  rcases hf with rfl | ⟨n, D, e, hD, rfl⟩
  · simpa using PhaseProduct.zero N ι
  let Q : TensorDecomposition AlgebraicComplex n := {D with scale := Units.mk0 c hc * D.scale}
  refine Or.inr ⟨n, Q, e, hD, ?_⟩
  funext x
  simp [Q, Tensor.reindex, TensorDecomposition.value, mul_assoc]

lemma PhaseProduct.tensor {N : ℕ} {ι κ : Type}
    {f : Tensor AlgebraicComplex ι} {g : Tensor AlgebraicComplex κ}
    (hf : PhaseProduct N f) (hg : PhaseProduct N g) : PhaseProduct N (Tensor.tensor f g) := by
  rcases hf with rfl | ⟨m, A, eA, hA, rfl⟩
  · simpa using PhaseProduct.zero N (ι ⊕ κ)
  rcases hg with rfl | ⟨n, B, eB, hB, rfl⟩
  · simpa using PhaseProduct.zero N (ι ⊕ κ)
  refine Or.inr ⟨m + n, A.append B,
    finSumFinEquiv.symm.trans (Equiv.sumCongr eA eB),
    TensorDecomposition.factors_append A B (fun _ h => EvenPhaseBlock N h) hA hB, ?_⟩
  rw [TensorDecomposition.value_append]
  funext x
  simp only [Tensor.reindex_apply, Signature.tensor_apply, Tensor.tensor_apply,
    Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]

end
end Paper2.HeightOne.PhaseCards
