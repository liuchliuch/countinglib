import Paper2.HeightOne.PhaseCards.PhaseProduct
import Mathlib.Data.Fintype.BigOperators

/-! Finite product assembly and literal selected-block extraction for source
Lemma 5.11. Empty products and the complete original normalization scalar are
retained. No contraction closure is used in these assembly proofs. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductDecomposition
noncomputable section
open Paper2 Tractable HeightOne.PhaseCards
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem phaseProduct_decomposition {N n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : PhaseProduct N f) (hn : f ≠ 0) :
    ∃ D : TensorDecomposition AlgebraicComplex n,
      (∀ i, EvenPhaseBlock N (D.factor i)) ∧ D.value = f := by
  rcases hf with hz | ⟨m,D,e,hD,he⟩
  · exact False.elim (hn hz)
  · exact ⟨D.reindex e,hD,he⟩

/-- A nested finite decomposition is flattened using the exact original
factor port equivalences. Its scale is the product of every inner scale. -/
def flatten {I : Type} [Fintype I] (r : I → ℕ)
    (D : (i : I) → TensorDecomposition AlgebraicComplex (r i)) :
    TensorDecomposition AlgebraicComplex (Fintype.card (Σ i : I, Fin (r i))) :=
  TensorDecomposition.ofFinite
    (fun p : Σ i : I, Fin (D i).count => (D p.1).arity p.2)
    (fun p => (D p.1).factor p.2)
    (((Equiv.sigmaAssoc (fun i j => Fin ((D i).arity j))).trans
      (Equiv.sigmaCongrRight (fun i => (D i).ports))).trans
        (Fintype.equivFin (Σ i : I, Fin (r i))))
    (∏ i, (D i).scale)

theorem flatten_value {I : Type} [Fintype I] (r : I → ℕ)
    (D : (i : I) → TensorDecomposition AlgebraicComplex (r i)) :
    Tensor.reindex (Fintype.equivFin (Σ i : I, Fin (r i))).symm (flatten r D).value =
      fun x => ∏ i : I, (D i).value (fun j => x ⟨i,j⟩) := by
  classical
  funext x
  simp only [Tensor.reindex_apply,flatten,TensorDecomposition.value_ofFinite,
    Equiv.trans_apply,Equiv.sigmaAssoc,Equiv.coe_fn_mk,
    Equiv.sigmaCongrRight_apply,Equiv.symm_apply_apply]
  rw [Fintype.prod_sigma]
  simp only [TensorDecomposition.value,Units.coe_prod]
  rw [Finset.prod_mul_distrib]

theorem flatten_blocks {I : Type} [Fintype I] {N : ℕ} (r : I → ℕ)
    (D : (i : I) → TensorDecomposition AlgebraicComplex (r i))
    (hD : ∀ i j, EvenPhaseBlock N ((D i).factor j)) :
    ∀ j, EvenPhaseBlock N ((flatten r D).factor j) := by
  intro j
  exact hD _ _

/-- All finite tensor products of phase products are phase products, including
the product indexed by the empty type and factors of arity zero. -/
theorem phaseProduct_sigma {I : Type} [Fintype I] {N : ℕ} (r : I → ℕ)
    (f : (i : I) → Signature AlgebraicComplex (r i))
    (hf : ∀ i, PhaseProduct N (f i)) :
    PhaseProduct N (fun x : (Σ i : I, Fin (r i)) → Bool =>
      ∏ i : I, f i (fun j => x ⟨i,j⟩)) := by
  classical
  by_cases hz : ∃ i, f i = 0
  · obtain ⟨i,hi⟩ := hz
    left
    funext x
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; rfl)
  · have hnonzero : ∀ i, f i ≠ 0 := by simpa only [not_exists] using hz
    have hex := fun i => phaseProduct_decomposition (f i) (hf i) (hnonzero i)
    choose D hD hval using hex
    right
    refine ⟨_,flatten r D,(Fintype.equivFin (Σ i : I, Fin (r i))).symm,
      flatten_blocks r D hD,?_⟩
    rw [flatten_value]
    simp only [hval]

/-- Assemble every actual ordered factor and the full scale of D. -/
theorem phaseProduct_value {N n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (hD : ∀ i, PhaseProduct N (D.factor i)) : PhaseProduct N D.value := by
  have h := (phaseProduct_sigma D.arity D.factor hD).reindex D.ports
  have hs := h.scale (D.scale : AlgebraicComplex)
  exact hs

abbrev Other {n : ℕ} (D : TensorDecomposition AlgebraicComplex n) (i : Fin D.count) :=
  {j : Fin D.count // j ≠ i}
abbrev OtherPorts {n : ℕ} (D : TensorDecomposition AlgebraicComplex n) (i : Fin D.count) :=
  Σ j : Other D i, Fin (D.arity j.val)

def remainder {n : ℕ} (D : TensorDecomposition AlgebraicComplex n) (i : Fin D.count) :
    Tensor AlgebraicComplex (OtherPorts D i) :=
  fun x => (D.scale : AlgebraicComplex) *
    ∏ j : Other D i, D.factor j.val (fun k => x ⟨j,k⟩)

def peelPorts {n : ℕ} (D : TensorDecomposition AlgebraicComplex n) (i : Fin D.count) :
    (Fin (D.arity i) ⊕ OtherPorts D i) ≃ Fin n :=
  (show (Fin (D.arity i) ⊕ OtherPorts D i) ≃
    (Σ j : Fin D.count, Fin (D.arity j)) from
    { toFun := Sum.elim (fun k => ⟨i,k⟩) (fun p => ⟨p.1.val,p.2⟩)
      invFun p := if hj : p.1 = i then .inl (Fin.cast (congrArg D.arity hj) p.2)
        else .inr ⟨⟨p.1,hj⟩,p.2⟩
      left_inv := by intro p; cases p with
        | inl k => simp
        | inr p => simp [p.1.property]
      right_inv := by
        rintro ⟨j,k⟩
        by_cases hj : j = i
        · subst j; simp
        · simp [hj] }).trans D.ports

@[simp] theorem peelPorts_left {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i : Fin D.count) (k : Fin (D.arity i)) :
    peelPorts D i (.inl k) = D.ports ⟨i,k⟩ := rfl

@[simp] theorem peelPorts_right {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i : Fin D.count) (p : OtherPorts D i) :
    peelPorts D i (.inr p) = D.ports ⟨p.1.val,p.2⟩ := rfl

theorem peel_value {n : ℕ} (D : TensorDecomposition AlgebraicComplex n) (i : Fin D.count) :
    Tensor.reindex (peelPorts D i) (Tensor.tensor (D.factor i) (remainder D i)) = D.value := by
  classical
  funext x
  simp only [Tensor.reindex_apply,Tensor.tensor_apply,remainder,TensorDecomposition.value,
    peelPorts_left,peelPorts_right]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  ring

theorem remainder_phaseProduct {N n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i : Fin D.count) (hD : ∀ j, PhaseProduct N (D.factor j)) :
    PhaseProduct N (remainder D i) :=
  (phaseProduct_sigma (fun j : Other D i => D.arity j.val)
    (fun j => D.factor j.val) (fun j => hD j.val)).scale D.scale

/-- One selected factor is exposed on its original ordered ports; the entire
other tensor and every original scalar remain in the phase-product remainder. -/
theorem peel {N n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i : Fin D.count) (hD : ∀ j, EvenPhaseBlock N (D.factor j)) :
    ∃ (g : Tensor AlgebraicComplex (OtherPorts D i))
      (e : (Fin (D.arity i) ⊕ OtherPorts D i) ≃ Fin n),
      PhaseProduct N g ∧
      (∀ k, e (.inl k) = D.ports ⟨i,k⟩) ∧
      Tensor.reindex e (Tensor.tensor (D.factor i) g) = D.value :=
  ⟨remainder D i,peelPorts D i,
    remainder_phaseProduct D i (fun j => PhaseProduct.of_block (hD j)),
    peelPorts_left D i,peel_value D i⟩

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductDecomposition

