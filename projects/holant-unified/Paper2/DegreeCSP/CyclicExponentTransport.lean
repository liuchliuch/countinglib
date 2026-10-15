import Paper2.DegreeCSP.CyclicPhaseCharacter

/-! Natural degrees and signed coordinate charges give the same cyclic
phase whenever their literal residues agree. -/
namespace Paper2.DegreeCSP.CyclicExponentTransport
open Tractable
noncomputable section

theorem nat_pow_eq_zpow {k : ℕ} (hk : 0<k)
    (theta : AlgebraicComplex) (hcycle : theta^k=1)
    (r : ℕ) (s : ℤ) (he : (r : ZMod k)=(s : ZMod k)) :
    theta^r=theta^s := by
  have ht : theta≠0 := by
    intro hz
    rw [hz,zero_pow (Nat.ne_of_gt hk)] at hcycle
    exact zero_ne_one hcycle
  have hd : (k : ℤ)∣(r : ℤ)-s := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [Int.cast_sub,Int.cast_natCast,sub_eq_zero] using he
  obtain ⟨m,hm⟩ := hd
  have hp : theta^((r : ℤ)-s)=1 := by
    rw [hm,zpow_mul,zpow_natCast,hcycle,one_zpow]
  rw [zpow_sub₀ ht,zpow_natCast] at hp
  exact (div_eq_one_iff_eq (zpow_ne_zero _ ht)).mp hp

end
end Paper2.DegreeCSP.CyclicExponentTransport
