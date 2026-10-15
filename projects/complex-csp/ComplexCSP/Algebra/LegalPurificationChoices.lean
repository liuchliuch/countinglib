import ComplexCSP.Algebra.LegalPurification

/-!
# Arbitrary legal generating choices

These data are the paper's three conditions: generators lie in the field of the
ambient nonzero values; their integer products are independent modulo torsion;
and each ambient value has a torsion-times-generator decomposition. Uniqueness
of exponents is a theorem. The exponent homomorphism on the entire generated
entry group is constructed through the quotient by torsion.
-/
namespace ComplexCSP.GeneratingSet

open Purification
open scoped BigOperators

noncomputable def fieldOfValues (S : Finset ℂˣ) : Subfield ℂ :=
  Subfield.closure ((fun u : ℂˣ => (u : ℂ)) '' (↑S : Set ℂˣ))

structure LegalGeneratingSet (S : Finset ℂˣ) where
  rank : ℕ
  generators : Fin rank → ℂˣ
  generators_in_field : ∀ i, (generators i : ℂ) ∈ fieldOfValues S
  independent : ∀ k : Fin rank → ℤ, IsOfFinOrder (∏ i, generators i ^ k i) → k = 0
  exponents : (a : S) → Fin rank → ℤ
  remainder_torsion : ∀ a : S, IsOfFinOrder (a.val / ∏ i, generators i ^ exponents a i)

namespace LegalGeneratingSet

variable {S : Finset ℂˣ}

abbrev EntryGroup (S : Finset ℂˣ) := Subgroup.closure (↑S : Set ℂˣ)
abbrev TorsionQuotient := ℂˣ ⧸ CommGroup.torsion ℂˣ

def quotientHom : ℂˣ →* TorsionQuotient := QuotientGroup.mk' (CommGroup.torsion ℂˣ)

@[simp] theorem quotientHom_eq_one_iff (x : ℂˣ) :
    quotientHom x = 1 ↔ IsOfFinOrder x := QuotientGroup.eq_one_iff x

noncomputable def generatorHom (L : LegalGeneratingSet S) :
    Multiplicative (Fin L.rank → ℤ) →* ℂˣ where
  toFun k := ∏ i, L.generators i ^ k.toAdd i
  map_one' := by simp
  map_mul' a b := by
    change (∏ i, L.generators i ^ (a.toAdd i + b.toAdd i)) = _
    simp only [zpow_add, Finset.prod_mul_distrib]

noncomputable def quotientGeneratorHom (L : LegalGeneratingSet S) :
    Multiplicative (Fin L.rank → ℤ) →* TorsionQuotient :=
  quotientHom.comp L.generatorHom

/-- Independence modulo torsion makes the quotient generator map injective. -/
theorem quotientGeneratorHom_injective (L : LegalGeneratingSet S) :
    Function.Injective L.quotientGeneratorHom := by
  intro a b hab
  have hq : L.quotientGeneratorHom (a / b) = 1 := by
    simp only [map_div, hab, div_self']
  have ht : IsOfFinOrder (L.generatorHom (a / b)) := (quotientHom_eq_one_iff _).mp hq
  have hk : (a / b).toAdd = 0 := L.independent _ ht
  have hone : a / b = 1 := hk
  exact div_eq_one.mp hone

/-- The legal decomposition puts each ambient entry in the quotient range. -/
theorem entry_quotient_eq (L : LegalGeneratingSet S) (a : S) :
    quotientHom a.val = L.quotientGeneratorHom (Multiplicative.ofAdd (L.exponents a)) := by
  have h := (quotientHom_eq_one_iff _).mpr (L.remainder_torsion a)
  rw [map_div] at h
  exact div_eq_one.mp h

/-- Closure extends quotient-range membership to all multiplicative combinations
of ambient entries, with negative powers included. -/
theorem quotient_mem_range (L : LegalGeneratingSet S) (x : EntryGroup S) :
    quotientHom x.val ∈ L.quotientGeneratorHom.range := by
  have hle : EntryGroup S ≤ L.quotientGeneratorHom.range.comap quotientHom := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    exact ⟨Multiplicative.ofAdd (L.exponents ⟨a, ha⟩), (L.entry_quotient_eq ⟨a, ha⟩).symm⟩
  exact hle x.property

noncomputable def quotientRangeHom (L : LegalGeneratingSet S) :
    EntryGroup S →* L.quotientGeneratorHom.range :=
  (quotientHom.comp (EntryGroup S).subtype).codRestrict _ L.quotient_mem_range

/-- The exponent extension is constructed by the inverse of an injective range
equivalence; representation independence is built into this construction. -/
noncomputable def exponentHom (L : LegalGeneratingSet S) :
    EntryGroup S →* Multiplicative (Fin L.rank → ℤ) :=
  (MonoidHom.ofInjective L.quotientGeneratorHom_injective).symm.toMonoidHom.comp L.quotientRangeHom

@[simp] theorem exponent_spec (L : LegalGeneratingSet S) (x : EntryGroup S) :
    L.quotientGeneratorHom (L.exponentHom x) = quotientHom x.val := by
  have h := (MonoidHom.ofInjective L.quotientGeneratorHom_injective).apply_symm_apply
    (L.quotientRangeHom x)
  exact congrArg Subtype.val h

/-- The extension agrees with every exponent prescribed by the legal choice. -/
theorem exponent_on_entry (L : LegalGeneratingSet S) (a : S) :
    L.exponentHom ⟨a.val, Subgroup.subset_closure a.property⟩ =
      Multiplicative.ofAdd (L.exponents a) := by
  apply L.quotientGeneratorHom_injective
  rw [L.exponent_spec]
  exact L.entry_quotient_eq a

/-- Its kernel is exactly the torsion of the intrinsic generated-entry group. -/
theorem exponent_kernel_torsion (L : LegalGeneratingSet S) (x : EntryGroup S) :
    L.exponentHom x = 1 ↔ IsOfFinOrder x := by
  have hiff : L.exponentHom x = 1 ↔ IsOfFinOrder x.val := by
    rw [← quotientHom_eq_one_iff, ← L.exponent_spec, ← map_one L.quotientGeneratorHom,
      L.quotientGeneratorHom_injective.eq_iff]
  exact hiff.trans ((EntryGroup S).subtype_injective.isOfFinOrder_iff)

/-- The exponent vector permitted by the legal decomposition is unique. -/
theorem exponents_unique (L : LegalGeneratingSet S) (a : S) (k : Fin L.rank → ℤ)
    (hk : IsOfFinOrder (a.val / ∏ i, L.generators i ^ k i)) : k = L.exponents a := by
  apply Multiplicative.ofAdd.injective
  apply L.quotientGeneratorHom_injective
  have hq := div_eq_one.mp (show quotientHom a.val /
    L.quotientGeneratorHom (Multiplicative.ofAdd k) = 1 from
      (map_div quotientHom _ _).symm.trans ((quotientHom_eq_one_iff _).mpr hk))
  exact hq.symm.trans (L.entry_quotient_eq a)

/-- The torsion remainder is an actual homomorphism. -/
noncomputable def phaseHom (L : LegalGeneratingSet S) : EntryGroup S →* ℂˣ :=
  (EntryGroup S).subtype / L.generatorHom.comp L.exponentHom

theorem phaseHom_finite_order (L : LegalGeneratingSet S) (x : EntryGroup S) :
    IsOfFinOrder (L.phaseHom x) := by
  apply (quotientHom_eq_one_iff _).mp
  change quotientHom (x.val / L.generatorHom (L.exponentHom x)) = 1
  rw [map_div]
  change quotientHom x.val / L.quotientGeneratorHom (L.exponentHom x) = 1
  rw [L.exponent_spec, div_self']

theorem phaseHom_torsion (L : LegalGeneratingSet S) {x : EntryGroup S}
    (hx : IsOfFinOrder x) : L.phaseHom x = x.val := by
  change x.val / L.generatorHom (L.exponentHom x) = x.val
  rw [(L.exponent_kernel_torsion x).mpr hx, map_one, div_one]

/-- The printed prime-based image for this arbitrary legal generating set. -/
noncomputable def purifiedHom (L : LegalGeneratingSet S) : EntryGroup S →* ℂˣ :=
  L.phaseHom * (complexPrimeProduct L.rank).comp L.exponentHom

theorem purifiedHom_norm_one_iff (L : LegalGeneratingSet S) (x : EntryGroup S) :
    ‖(L.purifiedHom x : ℂ)‖ = 1 ↔ IsOfFinOrder x := by
  change ‖(L.phaseHom x : ℂ) * (complexPrimeProduct L.rank (L.exponentHom x) : ℂ)‖ = 1 ↔ _
  have hp : ‖(L.phaseHom x : ℂ)‖ = 1 :=
    ((Units.coeHom ℂ).isOfFinOrder (L.phaseHom_finite_order x)).norm_eq_one
  rw [norm_mul, hp, one_mul, complexPrimeProduct_norm_one_iff]
  exact L.exponent_kernel_torsion x

theorem purifiedHom_torsion (L : LegalGeneratingSet S) {x : EntryGroup S}
    (hx : IsOfFinOrder x) : L.purifiedHom x = x.val := by
  change L.phaseHom x * complexPrimeProduct L.rank (L.exponentHom x) = x.val
  rw [(L.exponent_kernel_torsion x).mpr hx, map_one, mul_one, L.phaseHom_torsion hx]

theorem purifiedHom_injective (L : LegalGeneratingSet S) : Function.Injective L.purifiedHom := by
  intro x y hxy
  have hd : L.purifiedHom (x / y) = 1 := by simp only [map_div, hxy, div_self']
  have ht := (L.purifiedHom_norm_one_iff (x / y)).mp (show ‖(L.purifiedHom (x / y) : ℂ)‖ = 1 by
    rw [hd]; simp)
  have horig : (x / y).val = 1 := (L.purifiedHom_torsion ht).symm.trans hd
  have hgroup : x / y = 1 := Subtype.ext horig
  exact div_eq_one.mp hgroup

/-- An arbitrary legal choice produces the structural map required by the
already proved ambient-invariance and pure-to-original theorems. -/
noncomputable def purificationMap (L : LegalGeneratingSet S) :
    PurificationMap (EntryGroup S) (EntryGroup S).subtype where
  hom := L.purifiedHom
  injective := L.purifiedHom_injective
  fixes_torsion := fun _ hx => L.purifiedHom_torsion hx
  norm_one_iff := L.purifiedHom_norm_one_iff

end LegalGeneratingSet
end ComplexCSP.GeneratingSet
