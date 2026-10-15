import ComplexCSP.Algebra.EffectiveRootsPolynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Explicit integer coefficient bounds for monic divisors

All definitions computing bounds use only integer polynomial coefficient data.
Complex roots occur only in the proof that the bounds cover every divisor.
-/

namespace ComplexCSP.MonicIrreducibility

open Polynomial
open scoped BigOperators

/-- A natural coefficient bound for every monic divisor of a monic integer
polynomial. No factorization or root is computed. -/
def divisorBound (n B : ℕ) : ℕ := B ^ n * n.choose (n / 2)

/-- Every coefficient of every monic divisor satisfies a completely explicit
bound computed from the original integer polynomial. -/
theorem monic_divisor_coeff_bound (p q : Polynomial ℤ)
    (hp : p.Monic) (hq : q.Monic) (hqp : q ∣ p) (i : ℕ) :
    (q.coeff i).natAbs ≤ divisorBound p.natDegree
      (EffectiveRoots.integerCauchyBound p) := by
  let B := EffectiveRoots.integerCauchyBound p
  have hB : (1 : ℝ) ≤ B := by
    exact_mod_cast EffectiveRoots.integerCauchyBound_pos p
  have hroot : ∀ z ∈ (q.map (Int.castRingHom ℂ)).roots, ‖z‖ ≤ (B : ℝ) := by
    intro z hz
    have hz' := Multiset.mem_of_le
      (Polynomial.roots.le_of_dvd (hp.map (Int.castRingHom ℂ)).ne_zero
        (Polynomial.map_dvd (Int.castRingHom ℂ) hqp)) hz
    have heval := (Polynomial.mem_roots (hp.map (Int.castRingHom ℂ)).ne_zero).mp hz'
    apply EffectiveRoots.norm_root_le_integerCauchyBound p hp z
    simp only [Polynomial.IsRoot.def, Polynomial.eval_map] at heval
    exact heval
  have h := Polynomial.coeff_bdd_of_roots_le (Int.castRingHom ℂ) hq
    (IsAlgClosed.splits (q.map (Int.castRingHom ℂ))) (Polynomial.natDegree_le_of_dvd hqp hp.ne_zero)
    hroot i
  rw [max_eq_left hB] at h
  have h' : ((q.coeff i).natAbs : ℝ) ≤
      ((divisorBound p.natDegree B : ℕ) : ℝ) := by
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom, Complex.norm_intCast,
      Nat.cast_natAbs, Int.cast_abs, divisorBound, Nat.cast_mul, Nat.cast_pow] using h
  exact_mod_cast h'

end ComplexCSP.MonicIrreducibility
