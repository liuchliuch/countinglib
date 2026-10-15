import Paper2.Tractable.Scalars
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic

/-!
Characters on subgroups of a finite cyclic group extend to algebraic-complex
phases. Algebraic roots give divisibility of the group of nonzero scalars;
The inverse image in the integers has a positive generator; a root of its
character value supplies the extending phase.
-/

namespace Paper2.DegreeCSP.CyclicPhaseCharacter

open Tractable

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Every nonzero algebraic scalar admits a nonzero root of every positive
natural order. The witness stays in the actual algebraic-complex field. -/
theorem exists_unit_root (u : AlgebraicComplexˣ) {n : ℕ} (hn : n ≠ 0) :
    ∃ w : AlgebraicComplexˣ, w ^ n = u := by
  have : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (u : AlgebraicComplex)
    (Nat.pos_of_ne_zero hn)
  have hw0 : w ≠ 0 := by
    intro hz
    rw [hz, zero_pow hn] at hw
    exact u.ne_zero hw.symm
  refine ⟨Units.mk0 w hw0, ?_⟩
  apply Units.ext
  exact hw

/-- A character on an arbitrary subgroup of `ZMod k` is the restriction of a
single `k`-th root phase, using canonical natural representatives. -/
theorem extend_character {k : ℕ} (hk : 0 < k)
    (H : AddSubgroup (ZMod k))
    (χ : H →+ Additive AlgebraicComplexˣ) :
    ∃ θ : AlgebraicComplex, θ ^ k = 1 ∧
      ∀ h : H, (χ h).toMul.val = θ ^ h.val.val := by
  have : NeZero k := ⟨Nat.ne_of_gt hk⟩
  let J : AddSubgroup ℤ := H.comap (Int.castAddHom (ZMod k))
  obtain ⟨z, hz⟩ := AddSubgroup.exists_zmultiples_eq_of_zmultiples_eq_top
    Int.zmultiples_one J
  let d := z.natAbs
  have hdJ : AddSubgroup.zmultiples (d : ℤ) = J := by
    exact (Int.zmultiples_natAbs z).trans (by simpa [zsmul_one] using hz)
  have hkJ : (k : ℤ) ∈ J := by
    change ((k : ℤ) : ZMod k) ∈ H
    simpa only [Int.cast_natCast, ZMod.natCast_self] using H.zero_mem
  have hdk : d ∣ k := by
    exact_mod_cast (Int.mem_zmultiples_iff.mp (hdJ.symm ▸ hkJ))
  have hd : d ≠ 0 := by
    intro hz
    rw [hz, zero_dvd_iff] at hdk
    exact (Nat.ne_of_gt hk) hdk
  have hdH : (d : ZMod k) ∈ H := by
    have hj : (d : ℤ) ∈ J := hdJ ▸ AddSubgroup.mem_zmultiples (d : ℤ)
    simpa only [J, AddSubgroup.mem_comap, Int.coe_castAddHom, Int.cast_natCast] using hj
  let hgen : H := ⟨(d : ZMod k), hdH⟩
  obtain ⟨w, hw⟩ := exists_unit_root (χ hgen).toMul hd
  let θ : AlgebraicComplex := w.val
  refine ⟨θ, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hdk
    have hz : m • hgen = (0 : H) := by
      apply Subtype.ext
      change m • (d : ZMod k) = 0
      rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_comm, ← hm, ZMod.natCast_self]
    have hpow : (χ hgen).toMul ^ m = 1 := by
      have he := congrArg Additive.toMul (χ.map_nsmul m hgen)
      rw [hz, map_zero] at he
      exact he.symm
    have hwval := congrArg Units.val hw
    have hpval := congrArg Units.val hpow
    change θ ^ d = (χ hgen).toMul.val at hwval
    change (χ hgen).toMul.val ^ m = 1 at hpval
    rw [hm, pow_mul, hwval, hpval]
  · intro h
    have hhJ : (h.val.val : ℤ) ∈ J := by
      change ((h.val.val : ℤ) : ZMod k) ∈ H
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using h.property
    have hdh : d ∣ h.val.val := by
      exact_mod_cast (Int.mem_zmultiples_iff.mp (hdJ.symm ▸ hhJ))
    obtain ⟨m, hm⟩ := hdh
    have hh : m • hgen = h := by
      apply Subtype.ext
      change m • (d : ZMod k) = h.val
      rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_comm, ← hm, ZMod.natCast_zmod_val]
    have he := congrArg Additive.toMul (χ.map_nsmul m hgen)
    rw [hh] at he
    have hwval := congrArg Units.val hw
    have heval := congrArg Units.val he
    change θ ^ d = (χ hgen).toMul.val at hwval
    change (χ h).toMul.val = (χ hgen).toMul.val ^ m at heval
    rw [hm, pow_mul, hwval]
    exact heval


end

end Paper2.DegreeCSP.CyclicPhaseCharacter
