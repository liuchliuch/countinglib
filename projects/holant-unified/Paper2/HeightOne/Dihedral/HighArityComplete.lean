import Paper2.HeightOne.Dihedral.HighArityDeck
import Paper2.HeightOne.Dihedral.HighArityActualDeck

/-! The actual least-prime odd-dihedral branch at arity at least eight.
Every first card is derived from a retained real representative and its exact
selected binary factors. Signed matching surgery and four-card inversion then
produce a proper tensor factor of the original signature. -/
namespace Paper2.HeightOne.Dihedral
noncomputable section
open Cyclic Tractable ExactInput PhaseCards GroupSplit
open HighArity
set_option backward.isDefEq.respectTransparency false

variable {F : SignatureFamily AlgebraicComplex} {N : ℕ} [NeZero N]

/-- A genuine minimum prime of arity at least eight cannot survive complete
actual dihedral processing. No matching, ruling, phase extension, or analytic
factor conclusion is supplied as a hypothesis. -/
theorem minimum_higher_not_tensorPrime (C : XorCards F N) (L : Language)
    (hN : 3 ≤ N) (heven : ∀ f ∈ L.family,Even f.1)
    (hsafe : AllBinariesSafe L.family) {n : ℕ} (hn : 8 ≤ n)
    (hG : actualClasses L.family = dihedralPhaseClasses N)
    (hmin : LeastPrimeArity L.family n) (f : Signature AlgebraicComplex n)
    (hprocessed : (xorMenu C).Processed ⟨n,f⟩ L) : ¬ TensorPrime f := by
  intro hp
  obtain ⟨k,hk⟩ := heven ⟨n,f⟩ hprocessed.1
  change n = k+k at hk
  have hn' : n = 2*(k-3)+6 := by omega
  have hr : 1 ≤ k-3 := by omega
  cases hn'
  have hw := tensorPrime_action walshBasis.symm hp
  rw [walshBasis_inverse_action] at hw
  exact signed_deck_not_tensorPrime hN (k-3) hr (walshCoordinates f)
    (minimum_signed_first_cards C L heven hsafe hG hmin f hprocessed) hw

end
end Paper2.HeightOne.Dihedral
