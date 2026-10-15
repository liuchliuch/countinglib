import Paper2.HeightOne.PhaseCards.WalshTransport
import Paper2.PrimeFactorization
import Paper2.TensorAction

/-! Exact prime-factor hypotheses lift to the entire Walsh contraction, using
proved prime decomposition existence and its literal ordered tensor identity. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable EndpointSelfLoop
variable {ι : Type} [Fintype ι]

/-- Every positive prime factor of an actual tensor, in every ordered prime
factorization, has one Walsh support parity. -/
def PrimeFactorsHaveParity (f : Tensor AlgebraicComplex ι) : Prop :=
  ∀ (n : ℕ) (D : TensorDecomposition AlgebraicComplex n) (e : Fin n ≃ ι),
    Tensor.reindex e D.value = f →
    (∀ i, 0 < D.arity i) → (∀ i, TensorPrime (D.factor i)) →
    ∀ i, HasParity (walshCoordinates (D.factor i))

/-- Cyclic version: every such positive prime factor has even Walsh support. -/
def PrimeFactorsEven (f : Tensor AlgebraicComplex ι) : Prop :=
  ∀ (n : ℕ) (D : TensorDecomposition AlgebraicComplex n) (e : Fin n ≃ ι),
    Tensor.reindex e D.value = f →
    (∀ i, 0 < D.arity i) → (∀ i, TensorPrime (D.factor i)) →
    ∀ i, SupportedOnParity (walshCoordinates (D.factor i)) 0

lemma walshCoordinates_eq_coordinateAction {n : ℕ} (f : Signature AlgebraicComplex n) :
    walshCoordinates f = Signature.coordinateAction (fun _ => walshInv) f := by
  classical
  funext x
  unfold walshCoordinates action Signature.coordinateAction
  exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)

lemma decomposition_walsh (D : TensorDecomposition AlgebraicComplex (Fintype.card ι))
    (e : Fin (Fintype.card ι) ≃ ι) :
    Tensor.reindex e (D.mapAction walshInv).value =
      walshCoordinates (Tensor.reindex e D.value) := by
  rw [walshCoordinates_reindex, TensorDecomposition.value_mapAction]
  rw [walshCoordinates_eq_coordinateAction]

lemma prime_decomposition_ports (f : Tensor AlgebraicComplex ι)
    (hn : 0 < Fintype.card ι) (hf : f ≠ 0) :
    ∃ (D : TensorDecomposition AlgebraicComplex (Fintype.card ι)),
      Tensor.reindex (Fintype.equivFin ι).symm D.value = f ∧
      (∀ i, 0 < D.arity i) ∧ (∀ i, TensorPrime (D.factor i)) := by
  have hz : Tensor.reindex (Fintype.equivFin ι) f ≠ 0 := by
    intro h
    apply hf
    funext x
    have h' := congrFun h (fun j => x ((Fintype.equivFin ι).symm j))
    simpa only [Tensor.reindex_apply, Equiv.symm_apply_apply, Pi.zero_apply] using h'
  obtain ⟨D, hD, hpos, hprime⟩ :=
    exists_prime_decomposition (Tensor.reindex (Fintype.equivFin ι) f) hn hz
  exact ⟨D, by rw [hD]; simp, hpos, hprime⟩

theorem hasParity_of_primeFactors (f : Tensor AlgebraicComplex ι)
    (hn : 0 < Fintype.card ι) (hf : f ≠ 0) (h : PrimeFactorsHaveParity f) :
    HasParity (walshCoordinates f) := by
  obtain ⟨D, hval, hpos, hprime⟩ := prime_decomposition_ports f hn hf
  have hp := h _ D (Fintype.equivFin ι).symm hval hpos hprime
  have hd : HasParity (D.mapAction walshInv).value :=
    hasParity_decomposition _ (fun i _ => by
      simpa only [TensorDecomposition.mapAction, walshCoordinates_eq_coordinateAction] using hp i)
  have he := decomposition_walsh D (Fintype.equivFin ι).symm
  rw [hval] at he
  rw [← he]
  exact hasParity_reindex _ _ hd

theorem even_of_primeFactors (f : Tensor AlgebraicComplex ι)
    (hn : 0 < Fintype.card ι) (hf : f ≠ 0) (h : PrimeFactorsEven f) :
    SupportedOnParity (walshCoordinates f) 0 := by
  obtain ⟨D, hval, hpos, hprime⟩ := prime_decomposition_ports f hn hf
  have hp := h _ D (Fintype.equivFin ι).symm hval hpos hprime
  have hd : SupportedOnParity (D.mapAction walshInv).value 0 :=
    even_decomposition _ (fun i _ => by
      simpa only [TensorDecomposition.mapAction, walshCoordinates_eq_coordinateAction] using hp i)
  have he := decomposition_walsh D (Fintype.equivFin ι).symm
  rw [hval] at he
  rw [← he]
  exact supportedOnParity_reindex _ _ _ hd

/-- Primitive roots remain in the actual algebraic-complex field. This closes
the field bridge rather than assuming an analytic complex phase is algebraic. -/
lemma exists_algebraic_primitiveRoot (N : ℕ) (hN : N ≠ 0) :
    ∃ s : AlgebraicComplex, IsPrimitiveRoot s N := by
  let s := Complex.exp (2 * Real.pi * Complex.I / N)
  have hs : IsPrimitiveRoot s N := Complex.isPrimitiveRoot_exp N hN
  have hi : IsIntegral ℚ s :=
    IsIntegral.of_pow (by omega : 0 < N) (hs.pow_eq_one ▸ isIntegral_one)
  refine ⟨⟨s, hi⟩, ⟨?_, ?_⟩⟩
  · exact Subtype.ext hs.pow_eq_one
  · intro k hk
    exact hs.dvd_of_pow_eq_one k (congrArg Subtype.val hk)

end
end Paper2.HeightOne.PhaseCards
