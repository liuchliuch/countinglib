import ComplexCSP.Algebra.GeneratingSet
import Mathlib.NumberTheory.PrimeCounting

/-!
# The prime-exponent embedding

Distinct positive primes provide an injective multiplicative embedding of a
finite integer exponent lattice. Injectivity is proved coordinate by coordinate
with rational p-adic valuations, including negative exponents.
-/
namespace ComplexCSP.GeneratingSet

open scoped BigOperators

noncomputable def primeUnit (n : ℕ) : ℚˣ :=
  Units.mk0 (Nat.nth Nat.Prime n : ℚ) (by exact_mod_cast (Nat.prime_nth_prime n).ne_zero)

@[simp] theorem primeUnit_coe (n : ℕ) : (primeUnit n : ℚ) = Nat.nth Nat.Prime n := rfl

theorem primeUnit_pos (n : ℕ) : (0 : ℚ) < primeUnit n := by
  change (0 : ℚ) < (Nat.nth Nat.Prime n : ℚ)
  exact_mod_cast (Nat.prime_nth_prime n).pos

/-- Rational valuation as an honest group homomorphism on nonzero rationals. -/
noncomputable def rationalValuation (p : ℕ) [Fact p.Prime] : ℚˣ →* Multiplicative ℤ where
  toFun q := Multiplicative.ofAdd (padicValRat p q)
  map_one' := by simp
  map_mul' a b := by
    change padicValRat p ((a : ℚ) * (b : ℚ)) = padicValRat p a + padicValRat p b
    exact padicValRat.mul (Units.ne_zero a) (Units.ne_zero b)

/-- A fixed prime detects exactly its own coordinate among the first primes. -/
theorem valuation_primeUnit (i j : ℕ) :
    letI : Fact (Nat.nth Nat.Prime i).Prime := ⟨Nat.prime_nth_prime i⟩
    (rationalValuation (Nat.nth Nat.Prime i) (primeUnit j)).toAdd = if i = j then 1 else 0 := by
  classical
  letI : Fact (Nat.nth Nat.Prime i).Prime := ⟨Nat.prime_nth_prime i⟩
  dsimp [rationalValuation]
  by_cases hij : i = j
  · subst j
    simp [padicValRat.self (Nat.prime_nth_prime i).one_lt]
  · have hpij : Nat.nth Nat.Prime i ≠ Nat.nth Nat.Prime j :=
      fun h => hij (Nat.nth_injective Nat.infinite_setOf_prime h)
    letI : Fact (Nat.nth Nat.Prime j).Prime := ⟨Nat.prime_nth_prime j⟩
    simp only [padicValRat.of_nat, padicValNat_primes hpij, Int.natCast_zero,
      if_neg hij]

/-- The literal product of the first `n` primes to integral exponents. -/
noncomputable def primeProduct (n : ℕ) : Multiplicative (Fin n → ℤ) →* ℚˣ where
  toFun k := ∏ i, primeUnit i.val ^ k.toAdd i
  map_one' := by simp
  map_mul' a b := by
    change (∏ i, primeUnit i.val ^ (a.toAdd i + b.toAdd i)) = _
    simp only [zpow_add, Finset.prod_mul_distrib]

theorem valuation_primeProduct (n : ℕ) (k : Multiplicative (Fin n → ℤ)) (i : Fin n) :
    letI : Fact (Nat.nth Nat.Prime i.val).Prime := ⟨Nat.prime_nth_prime i.val⟩
    (rationalValuation (Nat.nth Nat.Prime i.val) (primeProduct n k)).toAdd = k.toAdd i := by
  classical
  letI : Fact (Nat.nth Nat.Prime i.val).Prime := ⟨Nat.prime_nth_prime i.val⟩
  change (rationalValuation (Nat.nth Nat.Prime i.val)
    (∏ j : Fin n, primeUnit j.val ^ k.toAdd j)).toAdd = _
  rw [map_prod]
  simp only [map_zpow, toAdd_prod, toAdd_zpow, valuation_primeUnit, zsmul_eq_mul]
  simp [Fin.val_inj, mul_ite]

/-- Unique factorization in positive rationals, including negative exponents. -/
theorem primeProduct_injective (n : ℕ) : Function.Injective (primeProduct n) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  funext i
  letI : Fact (Nat.nth Nat.Prime i.val).Prime := ⟨Nat.prime_nth_prime i.val⟩
  have h := congrArg (fun q => (rationalValuation (Nat.nth Nat.Prime i.val) q).toAdd) hab
  simpa only [valuation_primeProduct] using h

theorem primeProduct_eq_one_iff (n : ℕ) (k : Fin n → ℤ) :
    primeProduct n (Multiplicative.ofAdd k) = 1 ↔ k = 0 := by
  rw [← map_one (primeProduct n), (primeProduct_injective n).eq_iff]
  rfl

theorem primeProduct_pos (n : ℕ) (k : Multiplicative (Fin n → ℤ)) :
    (0 : ℚ) < primeProduct n k := by
  change (0 : ℚ) < (Units.coeHom ℚ) (∏ i, primeUnit i.val ^ k.toAdd i)
  rw [map_prod]
  simp only [Units.coeHom_apply, Units.val_zpow_eq_zpow_val]
  exact Finset.prod_pos fun i _ => zpow_pos (primeUnit_pos i.val) _

end ComplexCSP.GeneratingSet
