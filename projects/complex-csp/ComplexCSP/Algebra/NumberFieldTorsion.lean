import ComplexCSP.Structure.RowDetector
import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# Number-field torsion exponent

This discharges the mathematical existence of the root-of-unity-killing
exponent used by the detector. It relies on mathlib's proved finiteness of the
torsion subgroup of the ring-of-integers units. It does not implement an exact
number-field representation or an algorithm enumerating that subgroup.
-/

namespace ComplexCSP.RowDetector

open scoped NumberField BigOperators

/-- Any multiple of an exponent killing torsion also kills torsion. -/
theorem KillsTorsion.of_dvd {K : Type*} [Monoid K] {E F : ℕ}
    (hE : KillsTorsion K E) (hEF : E ∣ F) : KillsTorsion K F := by
  intro x hx
  obtain ⟨r, rfl⟩ := hEF
  rw [pow_mul, hE x hx, one_pow]

/-- A finite-order element of a field is an algebraic integer. -/
theorem isIntegral_int_of_isOfFinOrder {K : Type*} [Field K]
    (x : K) (hx : IsOfFinOrder x) : IsIntegral ℤ x := by
  obtain ⟨n, hn, hp⟩ := isOfFinOrder_iff_pow_eq_one.mp hx
  apply IsIntegral.of_pow hn
  rw [hp]
  exact isIntegral_one

/-- Mathlib's finite ring-of-integers torsion group kills every finite-order
field element, after lifting that element to an algebraic-integer unit. -/
theorem torsionOrder_killsTorsion (K : Type*) [Field K] [NumberField K] :
    KillsTorsion K (NumberField.Units.torsionOrder K) := by
  intro x hx
  let y : 𝓞 K := ⟨x, isIntegral_int_of_isOfFinOrder x hx⟩
  have hy : IsOfFinOrder y := by
    obtain ⟨n, hn, hp⟩ := isOfFinOrder_iff_pow_eq_one.mp hx
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    apply Subtype.ext
    exact hp
  let u : (𝓞 K)ˣ := hy.unit
  have humem : u ∈ NumberField.Units.torsion K := by
    apply (CommGroup.mem_torsion u).mpr
    apply Units.isOfFinOrder_val.mp
    exact hy
  have hupow : u ^ NumberField.Units.torsionOrder K = 1 := by
    exact NumberField.Units.pow_torsionOrder_eq_one K humem
  have hp := congrArg (fun z : (𝓞 K)ˣ ↦ (z : K)) hupow
  simp only [NumberField.Units.coe_pow, NumberField.Units.coe_one] at hp
  exact hp

/-- The paper's even positive torsion-killing exponent `lcm(2,e_K)`.
For finite cyclic root groups the group order is a valid choice of `e_K`. -/
noncomputable def fieldExponent (K : Type*) [Field K] [NumberField K] : ℕ :=
  Nat.lcm 2 (NumberField.Units.torsionOrder K)

theorem fieldExponent_ge_two (K : Type*) [Field K] [NumberField K] :
    2 ≤ fieldExponent K :=
  Nat.le_lcm_left 2 (NumberField.Units.torsionOrder_pos K)

theorem fieldExponent_pos (K : Type*) [Field K] [NumberField K] :
    0 < fieldExponent K := lt_of_lt_of_le (by omega) (fieldExponent_ge_two K)

theorem fieldExponent_even (K : Type*) [Field K] [NumberField K] :
    Even (fieldExponent K) := by
  exact even_iff_two_dvd.mpr (Nat.dvd_lcm_left 2 _)

theorem fieldExponent_killsTorsion (K : Type*) [Field K] [NumberField K] :
    KillsTorsion K (fieldExponent K) :=
  (torsionOrder_killsTorsion K).of_dvd (Nat.dvd_lcm_right 2 _)

/-- Number-field specialization of the bounded simultaneous detector search.
The torsion-killing exponent is constructed mathematically, not postulated. -/
theorem numberField_exists_simultaneous_detector_time {ι K : Type*}
    [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, Nonempty (κ i)] [Field K] [NumberField K]
    (u : ∀ i, κ i → K) (hu : ∀ i j, u i j ≠ 0) (L : ℕ) (hL : 0 < L) :
    ∃ t : ℕ, t < ∏ i, Fintype.card (κ i) ∧
      ∀ i, ComplexCSP.powerSum (fun j ↦ u i j ^ fieldExponent K) (1 + L * t) ≠ 0 :=
  exists_simultaneous_detector_time u hu (fieldExponent K) L
    (fieldExponent_pos K) hL (fieldExponent_killsTorsion K)

end ComplexCSP.RowDetector
