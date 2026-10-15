import Paper2.SourceFaithful.SourceStatements.PhaseProductPrimeAssembly

/-! Direct prime-factor reconstruction for a tensor already expressed in
Walsh coordinates. All nullary factors are retained in the actual scalar;
the zero tensor and empty port set need no factor premise. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductDecomposition
noncomputable section
open Paper2 Tractable HeightOne.PhaseCards
set_option backward.isDefEq.respectTransparency false

def PositivePrimeFactorsPhaseProduct {N : ℕ} {ι : Type} [Fintype ι]
    (f : Tensor AlgebraicComplex ι) : Prop :=
  ∀ (n : ℕ) (D : TensorDecomposition AlgebraicComplex n) (e : Fin n ≃ ι),
    Tensor.reindex e D.value = f →
    (∀ i, 0 < D.arity i) → (∀ i, TensorPrime (D.factor i)) →
    ∀ i, PhaseProduct N (D.factor i)

theorem phaseProduct_of_raw_prime_factors {N : ℕ} {ι : Type} [Fintype ι]
    (f : Tensor AlgebraicComplex ι)
    (h : PositivePrimeFactorsPhaseProduct (N:=N) f) : PhaseProduct N f := by
  classical
  by_cases hz : f = 0
  · subst f
    exact PhaseProduct.zero N ι
  by_cases hn : 0 < Fintype.card ι
  · obtain ⟨D,hval,hpos,hprime⟩ := prime_decomposition_ports f hn hz
    have hd : PhaseProduct N D.value := phaseProduct_value D
      (h _ D (Fintype.equivFin ι).symm hval hpos hprime)
    rw [← hval]
    exact hd.reindex _
  · have hcard : Fintype.card ι = 0 := by omega
    let : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    exact phaseProduct_nullary _

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductDecomposition

