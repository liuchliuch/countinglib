import Paper2.SourceFaithful.SourceStatements.PhaseProductDecomposition

/-! Expose two specified phase blocks with their actual original ordered
ports. Every other block and the original scale remain in the remainder. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductDecomposition
noncomputable section
open Paper2 Tractable HeightOne.PhaseCards
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev OtherTwo {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i j : Fin D.count) := {k : Fin D.count // k ≠ i ∧ k ≠ j}
abbrev OtherTwoPorts {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i j : Fin D.count) := Σ k : OtherTwo D i j, Fin (D.arity k.val)

def remainderTwo {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i j : Fin D.count) : Tensor AlgebraicComplex (OtherTwoPorts D i j) :=
  fun x => (D.scale : AlgebraicComplex) *
    ∏ k : OtherTwo D i j, D.factor k.val (fun a => x ⟨k,a⟩)

def peelTwoPorts {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i j : Fin D.count) (hij : i ≠ j) :
    ((Fin (D.arity i) ⊕ Fin (D.arity j)) ⊕ OtherTwoPorts D i j) ≃ Fin n :=
  (show ((Fin (D.arity i) ⊕ Fin (D.arity j)) ⊕ OtherTwoPorts D i j) ≃
    (Σ k : Fin D.count, Fin (D.arity k)) from
    { toFun := Sum.elim (Sum.elim (fun a => ⟨i,a⟩) (fun b => ⟨j,b⟩))
        (fun p => ⟨p.1.val,p.2⟩)
      invFun p := if hi : p.1 = i then
          .inl (.inl (Fin.cast (congrArg D.arity hi) p.2))
        else if hj : p.1 = j then
          .inl (.inr (Fin.cast (congrArg D.arity hj) p.2))
        else .inr ⟨⟨p.1,hi,hj⟩,p.2⟩
      left_inv := by
        intro p
        rcases p with (a | b) | p
        · simp
        · simp [hij.symm]
        · simp [p.1.property.1,p.1.property.2]
      right_inv := by
        rintro ⟨k,a⟩
        by_cases hi : k = i
        · subst k; simp
        · by_cases hj : k = j
          · subst k; simp [hij.symm]
          · simp [hi,hj] }).trans D.ports

@[simp] theorem peelTwoPorts_first {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i j : Fin D.count) (hij : i ≠ j) (a : Fin (D.arity i)) :
    peelTwoPorts D i j hij (.inl (.inl a)) = D.ports ⟨i,a⟩ := rfl

@[simp] theorem peelTwoPorts_second {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i j : Fin D.count) (hij : i ≠ j) (b : Fin (D.arity j)) :
    peelTwoPorts D i j hij (.inl (.inr b)) = D.ports ⟨j,b⟩ := rfl

@[simp] theorem peelTwoPorts_other {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i j : Fin D.count) (hij : i ≠ j) (p : OtherTwoPorts D i j) :
    peelTwoPorts D i j hij (.inr p) = D.ports ⟨p.1.val,p.2⟩ := rfl

lemma prod_peel_two {I : Type} [Fintype I] [DecidableEq I]
    (f : I → AlgebraicComplex) (i j : I) (hij : i ≠ j) :
    (∏ k : I, f k) = f i * f j * ∏ k : {k : I // k ≠ i ∧ k ≠ j}, f k.val := by
  classical
  have hrest : (∏ k ∈ (Finset.univ.erase i).erase j, f k) =
      ∏ k : {k : I // k ≠ i ∧ k ≠ j}, f k.val :=
    Finset.prod_subtype _ (fun k => by simp [and_comm]) f
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) f (a:=j) (by simp [hij.symm]),hrest]
  ring

theorem peel_two_value {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i j : Fin D.count) (hij : i ≠ j) :
    Tensor.reindex (peelTwoPorts D i j hij)
      (Tensor.tensor (Tensor.tensor (D.factor i) (D.factor j)) (remainderTwo D i j)) =
      D.value := by
  classical
  funext x
  simp only [Tensor.reindex_apply,Tensor.tensor_apply,remainderTwo,TensorDecomposition.value,
    peelTwoPorts_first,peelTwoPorts_second,peelTwoPorts_other]
  rw [prod_peel_two _ i j hij]
  ring

theorem remainderTwo_phaseProduct {N n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i j : Fin D.count) (hD : ∀ k, PhaseProduct N (D.factor k)) :
    PhaseProduct N (remainderTwo D i j) :=
  (phaseProduct_sigma (fun k : OtherTwo D i j => D.arity k.val)
    (fun k => D.factor k.val) (fun k => hD k.val)).scale D.scale

theorem peel_two {N n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i j : Fin D.count) (hij : i ≠ j) (hD : ∀ k, EvenPhaseBlock N (D.factor k)) :
    ∃ (g : Tensor AlgebraicComplex (OtherTwoPorts D i j))
      (e : ((Fin (D.arity i) ⊕ Fin (D.arity j)) ⊕ OtherTwoPorts D i j) ≃ Fin n),
      PhaseProduct N g ∧
      (∀ a, e (.inl (.inl a)) = D.ports ⟨i,a⟩) ∧
      (∀ b, e (.inl (.inr b)) = D.ports ⟨j,b⟩) ∧
      Tensor.reindex e (Tensor.tensor (Tensor.tensor (D.factor i) (D.factor j)) g) = D.value :=
  ⟨remainderTwo D i j,peelTwoPorts D i j hij,
    remainderTwo_phaseProduct D i j (fun k => PhaseProduct.of_block (hD k)),
    peelTwoPorts_first D i j hij,peelTwoPorts_second D i j hij,peel_two_value D i j hij⟩

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductDecomposition

