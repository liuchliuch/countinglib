import Paper2.HeightOne.Cyclic.Factorization
import Paper2.HeightOne.TensorPrimeTools

/-! Paper 2's higher odd-cyclic collapse: the actual minimum nonbinary prime
has arity exactly four. The proof retains real binary decompositions throughout. -/
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable ExactInput GroupSplit GroupSplit.MatrixGroup PhaseCards
variable {F : SignatureFamily AlgebraicComplex} {N : ℕ} [NeZero N]

/-- Any saturated nonzero minimum cyclic core of arity at least six is not
prime. This is a conclusion, not an accepted reconstruction hypothesis. -/
theorem minimum_higher_not_tensorPrime (P1 : Paper1DiagonalSlicesAccepted)
    (C : RotationCards F N) (L : Language) (hN : 3 ≤ N)
    (heven : ∀ f ∈ L.family, Even f.1) (hsafe : AllBinariesSafe L.family)
    {n : ℕ} (hn : 6 ≤ n) (hG : actualClasses L.family = cyclicPhaseClasses N)
    (hmin : LeastPrimeArity L.family n) (f : Signature AlgebraicComplex n) (hf : f ≠ 0)
    (hprocessed : (rotationMenu C).Processed ⟨n, f⟩ L) : ¬ TensorPrime f := by
  obtain ⟨D, hD, htwo⟩ := minimum_higher_binary_decomposition P1 C L hN heven hsafe hn hG hmin f hf hprocessed
  rw [← hD]
  exact binary_decomposition_not_tensorPrime D htwo (by omega)

/-- Source Theorem 5.22, with every matching, factor, and analytic coefficient
premise discharged from the actual processed root menu and minimum-prime data. -/
theorem minimum_cyclic_prime_arity_four (P1 : Paper1DiagonalSlicesAccepted)
    (C : RotationCards F N) (L : Language) (hN : 3 ≤ N)
    (heven : ∀ f ∈ L.family, Even f.1) (hsafe : AllBinariesSafe L.family)
    {n : ℕ} (hG : actualClasses L.family = cyclicPhaseClasses N)
    (hmin : LeastPrimeArity L.family n) (f : Signature AlgebraicComplex n)
    (hf : (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ L.family) (hprime : TensorPrime f)
    (hprocessed : (rotationMenu C).Processed ⟨n, f⟩ L) : n = 4 := by
  have hsmall : n < 6 := by
    by_contra hn
    exact minimum_higher_not_tensorPrime P1 C L hN heven hsafe (by omega) hG hmin f hprime.1 hprocessed hprime
  have he := heven ⟨n, f⟩ hf
  have hn3 := hmin.ge_three
  obtain ⟨k, hk⟩ := he
  change n = k + k at hk
  omega

end
end Paper2.HeightOne.Cyclic

