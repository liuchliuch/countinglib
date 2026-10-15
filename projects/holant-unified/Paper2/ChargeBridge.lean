import Paper2.ChargeProducts
import Paper2.EndpointSelfLoop
import Paper2.Mountain

/-!
The nonnegative-gcd and endpoint-self-loop parts of Lemma 4.1, joined on actual
coefficient tables. Both endpoint outputs are accompanied by finite derivations
using only reindexing and native-X self-loops from explicit repeated tensor
products. No factor extraction, oracle reduction, or hardness is assumed here.
-/
namespace Paper2.ChargeBridge
open scoped BigOperators
open ChargeProducts

variable {K : Type} [CommRing K] [NoZeroDivisors K] [Nontrivial K]

/-- Explicit tensor multiplicities followed by actual self-loop derivations
produce both gcd-height endpoint witnesses, with support divisibility retained. -/
theorem endpoints_from_charge_set (C : Finset ℤ)
    (hpos : ∃ p ∈ C, 0 < p) (hneg : ∃ n ∈ C, n < 0)
    (r : C → ℕ) (f : (c : C) → Signature K (r c))
    (x : (c : C) → Fin (r c) → Bool)
    (h2 : (2 : K) ≠ 0) (heven : ∀ c, Even (r c))
    (hsupport : ∀ c, f c (x c) ≠ 0)
    (hcharge : ∀ c, halfCharge (x c) = c.val)
    (hdiv : ∀ c, Tensor.HalfChargeDivisible (f c) (C.gcd Int.natAbs : ℕ)) :
    ∃ np nm : C → ℕ,
      ∃ P N : Signature K (2 * C.gcd Int.natAbs),
        EndpointSelfLoop.Reachable K (table np r f) P ∧
        EndpointSelfLoop.Reachable K (table nm r f) N ∧
        P (fun _ => true) ≠ 0 ∧ N (fun _ => false) ≠ 0 ∧
        Tensor.HalfChargeDivisible P (C.gcd Int.natAbs : ℕ) ∧
        Tensor.HalfChargeDivisible N (C.gcd Int.natAbs : ℕ) := by
  classical
  obtain ⟨np, nm, _, _, hp, hm⟩ :=
    ChargeSemigroup.exists_nonnegative_gcd_multiplicities hpos hneg
  let npC : C → ℕ := fun c => np c.val
  let nmC : C → ℕ := fun c => nm c.val
  have hpsum : (∑ c : C, (npC c : ℤ) * c.val) = (C.gcd Int.natAbs : ℕ) := by
    exact (C.sum_coe_sort (fun c => (np c : ℤ) * c)).trans hp
  have hmsum : (∑ c : C, (nmC c : ℤ) * c.val) = -((C.gcd Int.natAbs : ℕ) : ℤ) := by
    exact (C.sum_coe_sort (fun c => (nm c : ℤ) * c)).trans hm
  have hevenp : Even (Fintype.card (Ports npC r)) :=
    even_card_sigma (fun c => by simpa using heven c.1)
  have hevenm : Even (Fintype.card (Ports nmC r)) :=
    even_card_sigma (fun c => by simpa using heven c.1)
  obtain ⟨yp, hyps, hypc⟩ := supported_charge_combination npC r f x
    (fun c => c.val) _ heven hsupport hcharge hpsum
  obtain ⟨ym, hyms, hymc⟩ := supported_charge_combination nmC r f x
    (fun c => c.val) _ heven hsupport hcharge hmsum
  have hd := ChargeSemigroup.gcd_positive hpos
  have hdp := table_divisible npC r f _ heven hdiv
  have hdm := table_divisible nmC r f _ heven hdiv
  obtain ⟨P, hP, hPend, hPdiv⟩ := EndpointSelfLoop.positive_halfCharge_endpoint_divisible
    h2 (table npC r f) yp hyps hevenp hd hypc hdp
  obtain ⟨N, hN, hNend, hNdiv⟩ := EndpointSelfLoop.negative_halfCharge_endpoint_divisible
    h2 (table nmC r f) ym hyms hevenm hd hymc hdm
  exact ⟨npC, nmC, P, N, hP, hN, hPend, hNend, hPdiv, hNdiv⟩

end Paper2.ChargeBridge
