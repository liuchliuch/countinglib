import Paper2.HeightOne.Cyclic.TwoCopyRows
import Paper2.HeightOne.Cyclic.DressingPrime
import Paper2.HeightOne.Cyclic.BalancedPrimeFactors

/-! Complete odd-cyclic prime-quaternary closure. Every surviving branch
produces a literal native even four-port gadget with nonzero endpoints.
The two exceptional tensor products and the three-live-pair sum-zero branch
are excluded by proved ordered factorization and a proved actual two-copy row. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable PhaseCards Dihedral GroupSplit GroupSplit.MatrixGroup
open scoped BigOperators

lemma actual_balanced_eightVertex {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (C : RotationCards F N) (f : Signature AlgebraicComplex 4)
    (hf : NetworkRealizable F f) (r : Fin 4 → rootsOfUnity N AlgebraicComplex)
    (p : AlgebraicComplex) (s : Fin 3 → AlgebraicComplex)
    (he : rootWeighted r (walshCoordinates f) = balancedWalsh p s)
    (hsum : p + ∑ i, s i ≠ 0) :
    ∃ g : Signature AlgebraicComplex 4, NetworkRealizable F g ∧
      Paper2.HeightTwo.EvenSupport g ∧ g (fun _ => false) ≠ 0 ∧ g (fun _ => true) ≠ 0 := by
  obtain ⟨g,c,hg,hc,hw⟩ := actual_dressing_balanced C f hf r p s he
  have hnative : g = fun x => c * action walsh (balancedWalsh p s) x := by
    rw [← walsh_action_cancel g,hw,action_scalar]
  obtain ⟨heven,hzero,hone⟩ := inverseWalsh_balanced_eightVertex p s hsum
  refine ⟨g,hg,?_,?_,?_⟩
  · intro x hx
    apply heven x
    intro hz
    exact hx (by simp [hnative,hz])
  · rw [hnative]
    exact mul_ne_zero hc hzero
  · rw [hnative]
    exact mul_ne_zero hc hone

/-- The complete cyclic q4 closure requires only the actual safe cyclic group
and an actual prime source graph. All coefficient constraints are obtained
from real root representative contractions, then actually dressed. -/
theorem actual_prime_quaternary_eightVertex (P : Paper1PhasePencilAccepted)
    {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hN : 3 ≤ N) (hodd : Odd N) (hG : actualClasses F = cyclicPhaseClasses N)
    (hsafe : AllBinariesSafe F) (C : RotationCards F N)
    (f : Signature AlgebraicComplex 4) (hf : NetworkRealizable F f) (hp : TensorPrime f) :
    ∃ g : Signature AlgebraicComplex 4, NetworkRealizable F g ∧
      Paper2.HeightTwo.EvenSupport g ∧ g (fun _ => false) ≠ 0 ∧ g (fun _ => true) ≠ 0 := by
  classical
  let q := walshCoordinates f
  have heven : SupportedOnParity q 0 := actual_cyclic_quaternary_even hN hG hsafe f hf
  have hrows : QuaternaryRows N (q (fun _ => false)) (q (fun _ => true))
      (fun i => q (centralWord i (fun _ => false)))
      (fun i => q (flipAll (centralWord i (fun _ => false)))) :=
    actual_cyclic_quaternary_relations P hN hG hsafe f hf
  by_cases hzero : q (fun _ => false) = 0
  · have hone : q (fun _ => true) = 0 :=
      (paired_relation_endpoints hodd.pos (hrows 0).1 (hrows 0).2).mp hzero
    have hzrows : QuaternaryRows N 0 0
        (fun i => q (centralWord i (fun _ => false)))
        (fun i => q (flipAll (centralWord i (fun _ => false)))) := by
      simpa only [hzero,hone] using hrows
    obtain ⟨r,s,_,hnorm⟩ := zero_family_dressing_phases hodd q heven hzero hone hzrows
    have hprime : TensorPrime (balancedWalsh 0 s) := normalized_balanced_prime f hp r 0 s hnorm
    by_cases hsum : ∑ i, s i = 0
    · obtain ⟨h,c,hh,hc,hw⟩ := actual_dressing_balanced C f hf r 0 s hnorm
      exact False.elim (actual_zero_sum_three_pairs_impossible P hN hodd hG hsafe h hh c hc s
        (zero_sum_balanced_prime_all_nonzero s hsum hprime) hsum hw)
    · exact actual_balanced_eightVertex C f hf r 0 s hnorm (by simpa using hsum)
  · obtain ⟨r,s,hs,hnorm⟩ := live_family_dressing_phases hodd q heven hzero hrows
    have hprime := normalized_balanced_prime f hp r (q (fun _ => false)) s hnorm
    exact actual_balanced_eightVertex C f hf r _ s hnorm
      (live_balanced_prime_endpoint_sum _ hzero s hs hprime)

end
end Paper2.HeightOne.Cyclic
