import Paper2.HeightOne.Dihedral.ActualQuaternary
import Paper2.HeightOne.TensorPrimeTools
import Paper2.HeightOne.PhaseCards.WalshProduct

/-! The two-block dihedral quaternary form gives a literal ordered two-binary
factorization. Consequently an actual tensor-prime four-port signature has
exactly one complementary Walsh pair, with its genuine root phase retained. -/
namespace Paper2.HeightOne.Dihedral
noncomputable section
open Tractable PhaseCards PhasePencil GroupSplit GroupSplit.MatrixGroup

def blockPorts (i : Fin 3) : Fin 4 ≃ Fin 4 :=
  Equiv.ofBijective (fun j => ![0, i.succ, otherFirst i, otherSecond i] j)
    (by fin_cases i <;> decide)

lemma blockPorts_first (i : Fin 3) (j : Fin 2) :
    blockPorts i (Fin.castAdd 2 j) = firstPorts i j := by
  fin_cases j <;> rfl

lemma blockPorts_second (i : Fin 3) (j : Fin 2) :
    blockPorts i (Fin.natAdd 2 j) = secondPorts i j := by
  fin_cases j <;> rfl

theorem blockProduct_not_tensorPrime (i : Fin 3) (a : Word4)
    (p r s : AlgebraicComplex) : ¬ TensorPrime (blockProduct i a p r s) := by
  intro hp
  let A : Signature AlgebraicComplex 2 := fun x => p * twoPoint (a ∘ firstPorts i) r x
  let B : Signature AlgebraicComplex 2 := twoPoint (a ∘ secondPorts i) s
  apply hp.2 2 2 (by decide) (by decide) (blockPorts i) A B
  funext x
  change p * twoPoint (a ∘ firstPorts i) r (fun j => x (blockPorts i (Fin.castAdd 2 j))) *
    twoPoint (a ∘ secondPorts i) s (fun j => x (blockPorts i (Fin.natAdd 2 j))) = _
  simp only [blockPorts_first, blockPorts_second]
  rfl

lemma twoPoint_of_one_pair (f : Signature AlgebraicComplex 4) (a : Word4)
    (r : AlgebraicComplex) (htr : f (flipAll a) = r * f a)
    (hsupp : ∀ x, f x ≠ 0 → x = a ∨ x = flipAll a) :
    f = fun x => f a * twoPoint a r x := by
  classical
  have hna : a ≠ flipAll a := (sector_distinct 0 a).1
  funext x
  change f x = f a * (point a x + r * point (flipAll a) x)
  by_cases hxa : x = a
  · subst x
    simp [point, hna]
  by_cases hxt : x = flipAll a
  · subst x
    simp [point, htr, hna.symm]
    ring
  have hz : f x = 0 := by
    by_contra hn
    exact (hsupp x hn).elim hxa hxt
  simp [point, hz, hxa, hxt]

/-- Pure prime consequence of the complete coefficient deck. The second
support form is excluded by its actual ordered tensor factorization. -/
theorem tensorPrime_fullDeck_twoPoint {N : ℕ} (hodd : Odd N)
    (f : Signature AlgebraicComplex 4) (hp : TensorPrime f)
    (hpar : HasParity f) (hdeck : FullQuaternaryDeck N f) :
    ∃ (a : Word4) (p r : AlgebraicComplex), p ≠ 0 ∧ Root N r ∧
      f = fun x => p * twoPoint a r x := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, f a ≠ 0 := by
    by_contra h
    push Not at h
    exact hp.1 (funext h)
  obtain ⟨_, ⟨r, hr, htr⟩, hsupp | ⟨i, α, β, _, _, hx, hy, hti, hsupp⟩⟩ :=
    fullDeck_support_pairs hodd hpar hdeck a ha
  · exact ⟨a, f a, r, ha, hr, twoPoint_of_one_pair f a r htr hsupp⟩
  · have he := blockProduct_of_values f i a (f a) (-α) (-β) rfl hx hy
      (by simpa using hti) hsupp
    exact False.elim (blockProduct_not_tensorPrime i a (f a) (-α) (-β) (he ▸ hp))

/-- No analytic support premise is needed for an actual prime quaternary in
the complete safe odd-dihedral transfer group. -/
theorem actual_prime_quaternary_twoPoint (P : Paper1PhasePencilAccepted)
    {F : SignatureFamily AlgebraicComplex} {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (hG : actualClasses F = dihedralPhaseClasses N) (hsafe : AllBinariesSafe F)
    (f : Signature AlgebraicComplex 4) (hf : NetworkRealizable F f) (hp : TensorPrime f) :
    ∃ (a : Word4) (p r : AlgebraicComplex), p ≠ 0 ∧ Root N r ∧
      walshCoordinates f = fun x => p * twoPoint a r x := by
  have hprime := tensorPrime_action walshBasis.symm hp
  rw [walshBasis_inverse_action] at hprime
  exact tensorPrime_fullDeck_twoPoint hodd (walshCoordinates f) hprime
    (actual_quaternary_walsh_hasParity hN hG hsafe f hf)
    (actual_quaternary_fullDeck P hN hG hsafe f hf)

end
end Paper2.HeightOne.Dihedral

