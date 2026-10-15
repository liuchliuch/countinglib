import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The integer-combination step of arXiv:2610.00081v1, Lemma 4.1.
If a finite set of integer charges has both signs, its additive monoid already
contains their negatives. Consequently both signs of the gcd are obtainable
with nonnegative multiplicities. No tensor factor or gadget claim is asserted
by this arithmetic lemma.
-/

namespace Paper2
namespace ChargeSemigroup

/-- Finite sums of the available charges, with natural multiplicities. -/
def span (C : Finset ℤ) : AddSubmonoid ℤ := AddSubmonoid.closure (C : Set ℤ)

lemma generator_mem {C : Finset ℤ} {c : ℤ} (hc : c ∈ C) : c ∈ span C :=
  AddSubmonoid.subset_closure hc

/-- A charge of the opposite sign supplies a nonnegative expression for `-c`.
The coefficients used below are deliberately unreduced: this avoids division
and makes the zero-charge correction a literal integer identity. -/
lemma neg_generator_mem {C : Finset ℤ} (hpos : ∃ p ∈ C, 0 < p)
    (hneg : ∃ n ∈ C, n < 0) {c : ℤ} (hc : c ∈ C) : -c ∈ span C := by
  rcases hpos with ⟨p, hpC, hp⟩
  rcases hneg with ⟨n, hnC, hn⟩
  have hcM := generator_mem hc
  have hpM := generator_mem hpC
  have hnM := generator_mem hnC
  rcases lt_trichotomy c 0 with h | rfl | h
  · have h₁ : 0 ≤ -c := by omega
    have h₂ : 0 ≤ p - 1 := by omega
    have hm := (span C).add_mem ((span C).nsmul_mem hpM (-c).toNat)
      ((span C).nsmul_mem hcM (p - 1).toNat)
    have he : (-c).toNat • p + (p - 1).toNat • c = -c := by
      simp only [nsmul_eq_mul, Int.toNat_of_nonneg h₁, Int.toNat_of_nonneg h₂]
      ring
    exact he ▸ hm
  · simpa using (span C).zero_mem
  · have h₁ : 0 ≤ -n - 1 := by omega
    have h₂ : 0 ≤ c := le_of_lt h
    have hm := (span C).add_mem ((span C).nsmul_mem hcM (-n - 1).toNat)
      ((span C).nsmul_mem hnM c.toNat)
    have he : (-n - 1).toNat • c + c.toNat • n = -c := by
      simp only [nsmul_eq_mul, Int.toNat_of_nonneg h₁, Int.toNat_of_nonneg h₂]
      ring
    exact he ▸ hm

lemma neg_mem {C : Finset ℤ} (hpos : ∃ p ∈ C, 0 < p)
    (hneg : ∃ n ∈ C, n < 0) {z : ℤ} (hz : z ∈ span C) : -z ∈ span C := by
  induction hz using AddSubmonoid.closure_induction with
  | mem x hx => exact neg_generator_mem hpos hneg hx
  | zero => simpa using (span C).zero_mem
  | add x y hx hy ihx ihy => simpa only [neg_add] using (span C).add_mem ihx ihy

/-- This is not an additional closure: the carrier is still the monoid of
nonnegative combinations. Both signs of available generators make it a group. -/
def groupSpan (C : Finset ℤ) (hpos : ∃ p ∈ C, 0 < p)
    (hneg : ∃ n ∈ C, n < 0) : AddSubgroup ℤ where
  carrier := span C
  zero_mem' := (span C).zero_mem
  add_mem' := (span C).add_mem
  neg_mem' := neg_mem hpos hneg

lemma gcd_mem_addSubgroup (S : AddSubgroup ℤ) (C : Finset ℤ)
    (hC : ∀ c ∈ C, c ∈ S) : C.gcd id ∈ S := by
  induction C using Finset.induction_on with
  | empty => simpa using S.zero_mem
  | @insert a C ha ih =>
    have haS := hC a (Finset.mem_insert_self a C)
    have hgS := ih (fun c hc => hC c (Finset.mem_insert_of_mem hc))
    rw [Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.gcd_eq_gcd_ab]
    have h₁ := S.zsmul_mem haS (Int.gcdA a (C.gcd id))
    have h₂ := S.zsmul_mem hgS (Int.gcdB a (C.gcd id))
    simpa [zsmul_eq_mul, mul_comm] using S.add_mem h₁ h₂

lemma gcd_mem {C : Finset ℤ} (hpos : ∃ p ∈ C, 0 < p)
    (hneg : ∃ n ∈ C, n < 0) : C.gcd id ∈ span C :=
  gcd_mem_addSubgroup (groupSpan C hpos hneg) C (fun _ hc => generator_mem hc)

/-- The normalized integer gcd equals the usual natural gcd of absolute values. -/
lemma gcd_eq_natAbs_gcd (C : Finset ℤ) : C.gcd id = ((C.gcd Int.natAbs : ℕ) : ℤ) := by
  induction C using Finset.induction_on with
  | empty => simp
  | @insert a C ha ih =>
    rw [Finset.gcd_insert, Finset.gcd_insert, id_eq, ih, ← Int.coe_gcd]
    rfl

lemma gcd_positive {C : Finset ℤ} (hpos : ∃ p ∈ C, 0 < p) :
    0 < C.gcd Int.natAbs := by
  apply Nat.pos_of_ne_zero
  apply Finset.gcd_ne_zero_iff.mpr
  rcases hpos with ⟨p, hp, hpositive⟩
  exact ⟨p, hp, Int.natAbs_ne_zero.mpr (ne_of_gt hpositive)⟩

lemma gcd_dvd_charge {C : Finset ℤ} {c : ℤ} (hc : c ∈ C) :
    ((C.gcd Int.natAbs : ℕ) : ℤ) ∣ c :=
  Int.natCast_dvd.mpr (Finset.gcd_dvd hc)

/-- Exact natural multiplicity lists for both endpoints of the gcd height.
This is the arithmetic content of the first paragraph of Lemma 4.1. -/
theorem exists_nonnegative_gcd_multiplicities {C : Finset ℤ}
    (hpos : ∃ p ∈ C, 0 < p) (hneg : ∃ n ∈ C, n < 0) :
    ∃ nplus nminus : ℤ → ℕ,
      nplus.support ⊆ (C : Set ℤ) ∧ nminus.support ⊆ (C : Set ℤ) ∧
      (∑ c ∈ C, (nplus c : ℤ) * c) = ((C.gcd Int.natAbs : ℕ) : ℤ) ∧
      (∑ c ∈ C, (nminus c : ℤ) * c) = -((C.gcd Int.natAbs : ℕ) : ℤ) := by
  have hplus := gcd_mem hpos hneg
  have hminus := neg_mem hpos hneg hplus
  rw [span, AddSubmonoid.mem_closure_finset] at hplus hminus
  rcases hplus with ⟨np, hpS, hp⟩
  rcases hminus with ⟨nm, hmS, hm⟩
  refine ⟨np, nm, hpS, hmS, ?_, ?_⟩
  · simpa only [nsmul_eq_mul, gcd_eq_natAbs_gcd] using hp
  · simpa only [nsmul_eq_mul, gcd_eq_natAbs_gcd] using hm

end ChargeSemigroup
end Paper2
