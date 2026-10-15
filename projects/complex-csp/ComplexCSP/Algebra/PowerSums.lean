import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

/-!
# Finite power sums

Elementary cancellation control for the power-amplification arguments in
Cai--Chen complex CSP decidability. Finite indexed families represent multisets:
indices may carry equal values. No distinctness hypothesis is imposed.
-/

namespace ComplexCSP

open scoped BigOperators
open Polynomial

/-- The power sum of a finite indexed family, with multiplicities retained. -/
def powerSum {ι K : Type*} [Fintype ι] [CommSemiring K] (a : ι → K) (n : ℕ) : K :=
  ∑ i, a i ^ n

/-- A nonempty family of nonzero elements in a characteristic-zero domain has a
nonzero power sum among exponents `1,...,card ι`. This elementary characteristic-
polynomial argument supplies the finite power-sum contradiction in Lemma 8.2. -/
theorem exists_powerSum_ne_zero_bounded {ι K : Type*} [Fintype ι] [Nonempty ι]
    [CommRing K] [IsDomain K] [CharZero K] (a : ι → K) (ha : ∀ i, a i ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ n ≤ Fintype.card ι ∧ powerSum a n ≠ 0 := by
  classical
  by_contra! h
  let P : K[X] := ∏ i, (X - C (a i))
  have hdeg : P.natDegree ≤ Fintype.card ι := by
    simp [P]
  have hP0 : P.coeff 0 ≠ 0 := by
    simp only [P, Polynomial.coeff_zero_prod, coeff_sub, coeff_X_zero, coeff_C_zero,
      zero_sub]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ neg_ne_zero.mpr (ha i))
  have hroot (i : ι) : P.eval (a i) = 0 := by
    simp only [P, Polynomial.eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (a i))
  have hsum : (∑ i, P.eval (a i)) = P.coeff 0 * (Fintype.card ι : K) := by
    simp_rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
    rw [Finset.sum_comm, Finset.sum_range_succ']
    have hpos : (∑ k ∈ Finset.range (Fintype.card ι),
        ∑ i, P.coeff (k + 1) * a i ^ (k + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [← Finset.mul_sum]
      have hk' : k + 1 ≤ Fintype.card ι := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      rw [show (∑ i, a i ^ (k + 1)) = 0 from h (k + 1) (Nat.succ_pos k) hk']
      simp
    rw [hpos]
    simp [mul_comm]
  have hc : (Fintype.card ι : K) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  exact mul_ne_zero hP0 hc (by simpa [hroot] using hsum.symm)

/-- Multiplying finitely many power sums is itself a power sum, on the
finite Cartesian product of their indexing types. -/
theorem prod_powerSum_eq {ι K : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [CommSemiring K]
    (a : ∀ i, κ i → K) (n : ℕ) :
    (∏ i, powerSum (a i) n) = powerSum (fun x : ∀ i, κ i ↦ ∏ i, a i (x i)) n := by
  simp only [powerSum, Fintype.prod_sum, Finset.prod_pow]

/-- Explicitly bounded simultaneous nonvanishing. The upper bound is the product
of the multiset sizes. This avoids the Skolem--Mahler--Lech theorem in Lemma 7.1. -/
theorem exists_simultaneous_powerSum_ne_zero_bounded {ι K : Type*}
    [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, Nonempty (κ i)]
    [CommRing K] [IsDomain K] [CharZero K]
    (a : ∀ i, κ i → K) (ha : ∀ i j, a i j ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ n ≤ ∏ i, Fintype.card (κ i) ∧
      ∀ i, powerSum (a i) n ≠ 0 := by
  classical
  obtain ⟨n, hn, hbound, hnonzero⟩ := exists_powerSum_ne_zero_bounded
    (fun x : ∀ i, κ i ↦ ∏ i, a i (x i))
    (fun x ↦ Finset.prod_ne_zero_iff.mpr (fun i _ ↦ ha i (x i)))
  rw [← prod_powerSum_eq] at hnonzero
  exact ⟨n, hn, (Fintype.card_pi (α := κ)) ▸ hbound,
    fun i ↦ Finset.prod_ne_zero_iff.mp hnonzero i (Finset.mem_univ i)⟩

/-- There is a simultaneously nonvanishing positive multiple of any prescribed
positive integer, with an explicit upper bound. -/
theorem exists_simultaneous_powerSum_ne_zero_multiple {ι K : Type*}
    [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, Nonempty (κ i)]
    [CommRing K] [IsDomain K] [CharZero K]
    (a : ∀ i, κ i → K) (ha : ∀ i j, a i j ≠ 0)
    (q : ℕ) (_hq : 0 < q) :
    ∃ n : ℕ, q ≤ n ∧ n ≤ q * ∏ i, Fintype.card (κ i) ∧
      q ∣ n ∧ ∀ i, powerSum (a i) n ≠ 0 := by
  obtain ⟨m, hm, hbound, hnonzero⟩ := exists_simultaneous_powerSum_ne_zero_bounded
    (fun i j ↦ a i j ^ q) (fun i j ↦ pow_ne_zero q (ha i j))
  refine ⟨q * m, ?_, Nat.mul_le_mul_left q hbound, dvd_mul_right q m, ?_⟩
  · simpa only [Nat.mul_one] using Nat.mul_le_mul_left q hm
  · intro i
    simpa only [powerSum, ← pow_mul] using hnonzero i

/-- Arbitrarily large simultaneous nonvanishing, the infinitude content of
Lemma 7.1, with an additional finite search bound. -/
theorem exists_simultaneous_powerSum_ne_zero_above {ι K : Type*}
    [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, Nonempty (κ i)]
    [CommRing K] [IsDomain K] [CharZero K]
    (a : ∀ i, κ i → K) (ha : ∀ i j, a i j ≠ 0) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ n ≤ (N + 1) * ∏ i, Fintype.card (κ i) ∧
      ∀ i, powerSum (a i) n ≠ 0 := by
  obtain ⟨n, hn, hbound, _, hnonzero⟩ := exists_simultaneous_powerSum_ne_zero_multiple
    a ha (N + 1) (Nat.succ_pos N)
  exact ⟨n, hn, hbound, hnonzero⟩

/-- Full simultaneous infinitude over any characteristic-zero domain.
Algebraicity is unnecessary for the existence assertion. -/
theorem infinite_simultaneous_powerSum_ne_zero {ι K : Type*}
    [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, Nonempty (κ i)]
    [CommRing K] [IsDomain K] [CharZero K]
    (a : ∀ i, κ i → K) (ha : ∀ i j, a i j ≠ 0) :
    {n : ℕ | 0 < n ∧ ∀ i, powerSum (a i) n ≠ 0}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, _, hnonzero⟩ := exists_simultaneous_powerSum_ne_zero_above a ha N
  exact ⟨n, ⟨lt_of_le_of_lt (Nat.zero_le N) hn, hnonzero⟩, hn⟩

/-- Exhaustive finite search for the simultaneous exponent. The algorithm uses
only the supplied ring operations and exact equality decision; its bound is the
product of the indexing cardinalities. -/
def findSimultaneousPower {ι K : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [CommRing K] [DecidableEq K]
    (a : ∀ i, κ i → K) : Option ℕ :=
  (List.range ((∏ i, Fintype.card (κ i)) + 1)).find?
    (fun n ↦ decide (0 < n ∧ ∀ i, powerSum (a i) n ≠ 0))

/-- Every returned exponent is positive, within the proved bound, and works for
every input family. -/
theorem findSimultaneousPower_sound {ι K : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [CommRing K] [DecidableEq K]
    (a : ∀ i, κ i → K) {n : ℕ} (h : findSimultaneousPower a = some n) :
    0 < n ∧ n ≤ ∏ i, Fintype.card (κ i) ∧ ∀ i, powerSum (a i) n ≠ 0 := by
  have hp : 0 < n ∧ ∀ i, powerSum (a i) n ≠ 0 := by
    simpa only [decide_eq_true_eq] using List.find?_some h
  have hb : n < (∏ i, Fintype.card (κ i)) + 1 := by
    simpa only [List.mem_range] using List.mem_of_find?_eq_some h
  exact ⟨hp.1, Nat.lt_succ_iff.mp hb, hp.2⟩

/-- The bounded exhaustive search always returns a witness on the hypotheses of
Lemma 7.1. In particular, termination requires no oracle for zero sets of
linear recurrences. -/
theorem findSimultaneousPower_success {ι K : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, Nonempty (κ i)]
    [CommRing K] [IsDomain K] [CharZero K] [DecidableEq K]
    (a : ∀ i, κ i → K) (ha : ∀ i j, a i j ≠ 0) :
    (findSimultaneousPower a).isSome = true := by
  obtain ⟨n, hn, hb, hgood⟩ := exists_simultaneous_powerSum_ne_zero_bounded a ha
  apply List.find?_isSome.mpr
  exact ⟨n, List.mem_range.mpr (Nat.lt_succ_of_le hb), by simp [hn, hgood]⟩

/-- Enumerating a multiset retains every occurrence in its power sum. -/
theorem powerSum_multiset_get {K : Type*} [CommSemiring K] (A : Multiset K) (n : ℕ) :
    powerSum (fun i : Fin A.toList.length ↦ A.toList.get i) n =
      (A.map (fun x ↦ x ^ n)).sum := by
  conv_rhs => rw [← Multiset.coe_toList A, Multiset.map_coe, Multiset.sum_coe]
  change (∑ i : Fin A.toList.length, (A.toList.get i) ^ n) = _
  rw [← List.sum_ofFn]
  congr 1
  calc
    _ = (List.ofFn A.toList.get).map (fun x ↦ x ^ n) :=
      List.ofFn_comp' A.toList.get (fun x ↦ x ^ n)
    _ = _ := by rw [List.ofFn_get]

/-- Multiset form of the bounded finite power-sum contradiction (Lemma 8.2). -/
theorem exists_multiset_powerSum_ne_zero_bounded {K : Type*}
    [CommRing K] [IsDomain K] [CharZero K]
    (A : Multiset K) (hA : A ≠ 0) (ha : ∀ x ∈ A, x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ n ≤ A.card ∧ (A.map (fun x ↦ x ^ n)).sum ≠ 0 := by
  have hlen : 0 < A.toList.length := by
    simpa only [Multiset.length_toList] using Multiset.card_pos.mpr hA
  letI : Nonempty (Fin A.toList.length) := ⟨⟨0, hlen⟩⟩
  obtain ⟨n, hn, hb, hgood⟩ := exists_powerSum_ne_zero_bounded
    (fun i : Fin A.toList.length ↦ A.toList.get i)
    (fun i ↦ ha _ (Multiset.mem_toList.mp (List.get_mem _ i)))
  exact ⟨n, hn, by simpa only [Fintype.card_fin, Multiset.length_toList] using hb,
    by simpa only [powerSum_multiset_get] using hgood⟩

/-- Literal multiset formulation of Lemma 7.1. Its infinitude claim does not
require algebraicity or Skolem--Mahler--Lech. -/
theorem infinite_simultaneous_multiset_powerSum_ne_zero {ι K : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing K] [IsDomain K] [CharZero K]
    (A : ι → Multiset K) (hA : ∀ i, A i ≠ 0)
    (ha : ∀ i x, x ∈ A i → x ≠ 0) :
    {n : ℕ | 0 < n ∧ ∀ i, ((A i).map (fun x ↦ x ^ n)).sum ≠ 0}.Infinite := by
  letI (i : ι) : Nonempty (Fin (A i).toList.length) :=
    ⟨⟨0, by simpa only [Multiset.length_toList] using Multiset.card_pos.mpr (hA i)⟩⟩
  simpa only [powerSum_multiset_get] using infinite_simultaneous_powerSum_ne_zero
    (fun i (j : Fin (A i).toList.length) ↦ (A i).toList.get j)
    (fun i j ↦ ha i _ (Multiset.mem_toList.mp (List.get_mem _ j)))

/-- A finite weighted exponential sum. -/
def weightedPowerSum {ι K : Type*} [Fintype ι] [CommSemiring K]
    (a b : ι → K) (n : ℕ) : K := ∑ i, a i * b i ^ n

/-- Vandermonde consequence: distinct bases and at least one nonzero coefficient
cannot produce `n` consecutive initial zeros. -/
theorem exists_weightedPowerSum_ne_zero {K : Type*} [CommRing K] [IsDomain K]
    {n : ℕ} (a b : Fin n → K) (hb : Function.Injective b)
    (ha : ∃ i, a i ≠ 0) :
    ∃ k : Fin n, weightedPowerSum a b k ≠ 0 := by
  by_contra! h
  have hz : a = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hb h
  obtain ⟨i, hi⟩ := ha
  exact hi (congrFun hz i)

/-- Vandermonde consequence at every starting position. This is weaker than
finite zero set: isolated zeros at arbitrarily large indices are not excluded. -/
theorem exists_weightedPowerSum_ne_zero_in_block {K : Type*}
    [CommRing K] [IsDomain K] {n : ℕ} (a b : Fin n → K)
    (hb : Function.Injective b) (hb0 : ∀ i, b i ≠ 0)
    (ha : ∃ i, a i ≠ 0) (N : ℕ) :
    ∃ k : Fin n, weightedPowerSum a b (N + k) ≠ 0 := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨k, hk⟩ := exists_weightedPowerSum_ne_zero (fun j ↦ a j * b j ^ N) b hb
    ⟨i, mul_ne_zero hi (pow_ne_zero N (hb0 i))⟩
  refine ⟨k, ?_⟩
  simpa only [weightedPowerSum, pow_add, mul_assoc] using hk

/-- The elementary Vandermonde half of Lemma 8.3: if raising the bases to `m`
preserves distinctness, no arithmetic progression of step `m` can eventually
consist entirely of zeros. A theorem controlling general recurrence zero sets
is still needed to deduce their finiteness. -/
theorem exists_weightedPowerSum_ne_zero_on_progression {K : Type*}
    [CommRing K] [IsDomain K] {n : ℕ} (a b : Fin n → K)
    (hb0 : ∀ i, b i ≠ 0) (ha : ∃ i, a i ≠ 0)
    (r m N : ℕ) (hm : Function.Injective (fun i ↦ b i ^ m)) :
    ∃ k : Fin n, weightedPowerSum a b (r + m * (N + k)) ≠ 0 := by
  obtain ⟨i, hi⟩ := ha
  obtain ⟨k, hk⟩ := exists_weightedPowerSum_ne_zero_in_block
    (fun j ↦ a j * b j ^ r) (fun j ↦ b j ^ m) hm
    (fun j ↦ pow_ne_zero m (hb0 j))
    ⟨i, mul_ne_zero hi (pow_ne_zero r (hb0 i))⟩ N
  refine ⟨k, ?_⟩
  simpa only [weightedPowerSum, pow_add, pow_mul, mul_assoc] using hk

/-- The initial-block Vandermonde consequence on an arbitrary finite index type. -/
theorem exists_weightedPowerSum_ne_zero_fintype {ι K : Type*} [Fintype ι]
    [CommRing K] [IsDomain K] (a b : ι → K) (hb : Function.Injective b)
    (ha : ∃ i, a i ≠ 0) :
    ∃ k : ℕ, k < Fintype.card ι ∧ weightedPowerSum a b k ≠ 0 := by
  classical
  let e := (Fintype.equivFin ι).symm
  have ha' : ∃ i, a (e i) ≠ 0 := by
    obtain ⟨i, hi⟩ := ha
    exact ⟨e.symm i, by simpa using hi⟩
  obtain ⟨k, hk⟩ := exists_weightedPowerSum_ne_zero (a ∘ e) (b ∘ e)
    (hb.comp e.injective) ha'
  refine ⟨k, k.isLt, ?_⟩
  change (∑ i, a (e i) * b (e i) ^ (k : ℕ)) ≠ 0 at hk
  rw [e.sum_comp (fun i ↦ a i * b i ^ (k : ℕ))] at hk
  exact hk

/-- Non-root-of-unity ratios imply distinctness after every positive power. -/
theorem injective_pow_of_no_torsion_ratios {ι K : Type*} [Field K]
    (b : ι → K) (hb : ∀ i, b i ≠ 0)
    (ht : ∀ i j, i ≠ j → ¬ IsOfFinOrder (b i / b j))
    (m : ℕ) (hm : 0 < m) : Function.Injective (fun i ↦ b i ^ m) := by
  intro i j hij
  dsimp only at hij
  by_contra hne
  apply ht i j hne
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨m, hm, ?_⟩
  rw [div_pow, hij, div_self (pow_ne_zero m (hb j))]

end ComplexCSP
