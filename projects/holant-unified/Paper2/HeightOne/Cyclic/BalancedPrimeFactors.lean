import Paper2.HeightOne.Cyclic.BalancedCoefficients
import Paper2.HeightOne.Cyclic.ThreePairObstruction
import Paper2.HeightOne.Dihedral.QuaternaryPrime

/-! The two exceptional balanced cyclic tables have literal ordered binary
factorizations. They cannot occur as a tensor-prime four-port output. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable PhaseCards Dihedral
open scoped BigOperators

lemma balanced_one_pair_blockProduct (p : AlgebraicComplex) (i : Fin 3) :
    balancedWalsh p (fun j => if j = i then -p else 0) =
      blockProduct i (fun _ => false) p (-1) (-1) := by
  rw [balancedWalsh_eq_coefficients]
  funext x
  rw [blockProduct_expand]
  fin_cases i <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [balancedCoefficients,point,centralWord,flipPair,flipAll,
    funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]
  all_goals ring

lemma balanced_one_pair_not_prime (p : AlgebraicComplex) (i : Fin 3) :
    ¬ TensorPrime (balancedWalsh p (fun j => if j = i then -p else 0)) := by
  rw [balanced_one_pair_blockProduct]
  exact blockProduct_not_tensorPrime i (fun _ => false) p (-1) (-1)

/-- A live balanced prime has a nonzero native endpoint sum. The only
vanishing possibility has one live complementary pair and factors. -/
theorem live_balanced_prime_endpoint_sum (p : AlgebraicComplex) (hp : p ≠ 0)
    (s : Fin 3 → AlgebraicComplex) (hs : ∀ i, s i = 0 ∨ s i = -p)
    (hprime : TensorPrime (balancedWalsh p s)) : p + ∑ i, s i ≠ 0 := by
  intro hsum
  simp only [Fin.sum_univ_three] at hsum
  rcases hs 0 with h0 | h0 <;> rcases hs 1 with h1 | h1 <;> rcases hs 2 with h2 | h2
  all_goals try (apply hp; linear_combination hsum - h0 - h1 - h2)
  all_goals try (apply hp; linear_combination -hsum + h0 + h1 + h2)
  all_goals try (apply hp; linear_combination (-1/2 : AlgebraicComplex) * (hsum - h0 - h1 - h2))
  · have he : s = fun j : Fin 3 => if j = 2 then -p else 0 := by
      funext j; fin_cases j <;> simp_all
    exact balanced_one_pair_not_prime p 2 (he ▸ hprime)
  · have he : s = fun j : Fin 3 => if j = 1 then -p else 0 := by
      funext j; fin_cases j <;> simp_all
    exact balanced_one_pair_not_prime p 1 (he ▸ hprime)
  · have he : s = fun j : Fin 3 => if j = 0 then -p else 0 := by
      funext j; fin_cases j <;> simp_all
    exact balanced_one_pair_not_prime p 0 (he ▸ hprime)

lemma zero_sum_missing_pair_blockProduct (s : Fin 3 → AlgebraicComplex)
    (i : Fin 3) (hi : s i = 0) (hs : ∑ j, s j = 0) :
    balancedWalsh 0 s = blockProduct i (centralWord (nextPair i) (fun _ => false))
      (s (nextPair i)) (-1) (-1) := by
  rw [balancedWalsh_eq_coefficients]
  have hsum : s 0 + s 1 + s 2 = 0 := by simpa only [Fin.sum_univ_three] using hs
  funext x
  rw [blockProduct_expand]
  fin_cases i <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [balancedCoefficients,point,centralWord,flipPair,flipAll,nextPair,
    funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3] at *
  all_goals first | assumption | (linear_combination hsum - hi) | (linear_combination hsum + hi) | ring

/-- Under sum zero, primality rules out every missing central pair, including
the all-zero table. The remaining three-live-pair branch is excluded by its
actual two-copy RN row in TwoCopyRows. -/
theorem zero_sum_balanced_prime_all_nonzero (s : Fin 3 → AlgebraicComplex)
    (hs : ∑ i, s i = 0) (hp : TensorPrime (balancedWalsh 0 s)) : ∀ i, s i ≠ 0 := by
  intro i hi
  rw [zero_sum_missing_pair_blockProduct s i hi hs] at hp
  exact blockProduct_not_tensorPrime _ _ _ _ _ hp

end
end Paper2.HeightOne.Cyclic
