import Paper2.SourceFaithful.SourceStatements.PhaseProductPeelTwo
import Paper2.HeightOne.PhaseCards.PrimeParity

/-! The prime-factor consequence of source Lemma 5.11, including zero and
nullary tensors. The selected ordered prime decomposition is constructed;
its full scalar and all literal factor ports are retained. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductDecomposition
noncomputable section
open Paper2 Tractable HeightOne.PhaseCards
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem phaseProduct_constant {N : ℕ} {ι : Type} [IsEmpty ι] (c : AlgebraicComplex) :
    PhaseProduct N (fun _ : ι → Bool => c) := by
  classical
  by_cases hc : c = 0
  · subst c
    exact PhaseProduct.zero N ι
  · let D : TensorDecomposition AlgebraicComplex 0 :=
      { count := 0
        arity := Fin.elim0
        factor := fun i => Fin.elim0 i
        ports := Equiv.equivOfIsEmpty _ _
        scale := Units.mk0 c hc }
    right
    refine ⟨0,D,Equiv.equivOfIsEmpty _ _,(fun i => Fin.elim0 i),?_⟩
    funext x
    simp [D,Tensor.reindex_apply,TensorDecomposition.value]

theorem phaseProduct_nullary {N : ℕ} {ι : Type} [IsEmpty ι]
    (f : Tensor AlgebraicComplex ι) : PhaseProduct N f := by
  have he : f = fun _ => f (fun _ => false) := by
    funext x
    exact congrArg f (Subsingleton.elim _ _)
  rw [he]
  exact phaseProduct_constant _

/-- Every positive tensor-prime factor in every actual ordered decomposition
has its Walsh tensor in the source phase-product class. Nullary scalar factors
impose no membership requirement. -/
def PrimeFactorsPhaseProduct {N : ℕ} {ι : Type} [Fintype ι]
    (f : Tensor AlgebraicComplex ι) : Prop :=
  ∀ (n : ℕ) (D : TensorDecomposition AlgebraicComplex n) (e : Fin n ≃ ι),
    Tensor.reindex e D.value = f →
    (∀ i, 0 < D.arity i) → (∀ i, TensorPrime (D.factor i)) →
    ∀ i, PhaseProduct N (walshCoordinates (D.factor i))

/-- Literal final clause of source Lemma 5.11. No chosen decomposition, factor
availability, positive arity or nonzero premise is supplied by the caller. -/
theorem phaseProduct_of_prime_factors {N : ℕ} {ι : Type} [Fintype ι]
    (f : Tensor AlgebraicComplex ι) (h : PrimeFactorsPhaseProduct (N:=N) f) :
    PhaseProduct N (walshCoordinates f) := by
  classical
  by_cases hz : f = 0
  · subst f
    have hw : walshCoordinates (0 : Tensor AlgebraicComplex ι) = 0 := by
      funext x
      simp [walshCoordinates,action]
    rw [hw]
    exact PhaseProduct.zero N ι
  by_cases hn : 0 < Fintype.card ι
  · obtain ⟨D,hval,hpos,hprime⟩ := prime_decomposition_ports f hn hz
    have hp := h _ D (Fintype.equivFin ι).symm hval hpos hprime
    have hd : PhaseProduct N (D.mapAction walshInv).value :=
      phaseProduct_value _ (fun i => by
        simpa only [TensorDecomposition.mapAction,walshCoordinates_eq_coordinateAction] using hp i)
    have he := decomposition_walsh D (Fintype.equivFin ι).symm
    rw [hval] at he
    rw [← he]
    exact hd.reindex _
  · have hcard : Fintype.card ι = 0 := by omega
    let : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    exact phaseProduct_nullary _

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductDecomposition

