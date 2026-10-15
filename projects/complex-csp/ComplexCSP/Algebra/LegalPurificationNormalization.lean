import ComplexCSP.Algebra.LegalPurificationExistence

/-!
# Positive integral normalization of legal purifications

A common positive natural denominator clears the finitely many positive rational
prime amplitudes. The resulting entries are proved to be natural-number
multiples of roots of unity, exactly the paper's definition of purity.
-/
namespace ComplexCSP.GeneratingSet

open scoped BigOperators

/-- An actual common positive denominator, valid for any finite positive-rational
family. The proof constructs the product of their denominators. -/
theorem positive_common_denominator {I : Type*} [Fintype I] (r : I → ℚ)
    (hr : ∀ i, 0 < r i) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∃ n : ℕ, 0 < n ∧ (N : ℚ) * r i = n := by
  classical
  let N : ℕ := ∏ i, (r i).den
  have hN : 0 < N := Finset.prod_pos fun i _ => (r i).den_pos
  refine ⟨N, hN, ?_⟩
  intro i
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun j => (r j).den) (Finset.mem_univ i)
  have hmpos : 0 < m := by
    have h : 0 < (r i).den * m := by rw [← hm]; exact hN
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, mul_zero] at h
    omega
  have hnum : 0 < (r i).num := Rat.num_pos.mpr (hr i)
  have hcast : ((r i).num.natAbs : ℚ) = ((r i).num : ℚ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_pos hnum]
  refine ⟨m * (r i).num.natAbs, Nat.mul_pos hmpos (Int.natAbs_pos.mpr (ne_of_gt hnum)), ?_⟩
  calc
    (N : ℚ) * r i = ((r i).den * m : ℕ) * r i := by rw [← hm]
    _ = (m : ℚ) * ((r i).den * r i) := by push_cast; ring
    _ = (m : ℚ) * (r i).num := by rw [Rat.den_mul_eq_num]
    _ = (m * (r i).num.natAbs : ℕ) := by push_cast; rw [hcast]

/-- The numerical purity definition: a natural number times a root of unity. -/
def IsPureValue (z : ℂ) : Prop := ∃ n : ℕ, ∃ ζ : ℂ, IsOfFinOrder ζ ∧ z = n * ζ

@[simp] theorem zero_isPureValue : IsPureValue 0 := ⟨0, 1, isOfFinOrder_iff_pow_eq_one.mpr ⟨1, by omega, by simp⟩, by simp⟩

namespace LegalGeneratingSet
variable {S : Finset ℂˣ}

/-- The constructed extension gives exactly the paper's printed entry, with the
prescribed exponent vector and its original torsion remainder. -/
theorem purifiedHom_on_entry (L : LegalGeneratingSet S) (a : S) :
    (L.purifiedHom ⟨a.val, Subgroup.subset_closure a.property⟩ : ℂ) =
      ((a.val / ∏ i, L.generators i ^ L.exponents a i : ℂˣ) : ℂ) *
        ((primeProduct L.rank (Multiplicative.ofAdd (L.exponents a)) : ℚ) : ℂ) := by
  change ((a.val / L.generatorHom (L.exponentHom ⟨a.val, Subgroup.subset_closure a.property⟩) : ℂˣ) : ℂ) *
    (complexPrimeProduct L.rank (L.exponentHom ⟨a.val, Subgroup.subset_closure a.property⟩) : ℂ) = _
  rw [L.exponent_on_entry]
  rfl

/-- One positive natural table-wide normalization makes every ambient nonzero
entry pure. Empty ambient sets are allowed and cause no exceptional assumption. -/
theorem exists_pure_normalization (L : LegalGeneratingSet S) :
    ∃ N : ℕ, 0 < N ∧ ∀ a : S,
      IsPureValue ((N : ℂ) * (L.purifiedHom ⟨a.val, Subgroup.subset_closure a.property⟩ : ℂ)) := by
  obtain ⟨N, hN, h⟩ := positive_common_denominator
    (fun a : S => (primeProduct L.rank (Multiplicative.ofAdd (L.exponents a)) : ℚ))
    (fun a => primeProduct_pos L.rank _)
  refine ⟨N, hN, ?_⟩
  intro a
  obtain ⟨n, _, hn⟩ := h a
  let θ : ℂˣ := a.val / ∏ i, L.generators i ^ L.exponents a i
  have ht : IsOfFinOrder (θ : ℂ) := (Units.coeHom ℂ).isOfFinOrder (L.remainder_torsion a)
  refine ⟨n, θ, ht, ?_⟩
  rw [L.purifiedHom_on_entry]
  have hc : (N : ℂ) * ((primeProduct L.rank (Multiplicative.ofAdd (L.exponents a)) : ℚ) : ℂ) = n := by
    exact_mod_cast hn
  change (N : ℂ) * ((θ : ℂ) * _) = (n : ℂ) * (θ : ℂ)
  rw [mul_left_comm, hc, mul_comm]

end LegalGeneratingSet
end ComplexCSP.GeneratingSet
