module
public import Paper2.Certificates.DihedralSupport.Core
public import Mathlib.Tactic.Ring

@[expose] public section
namespace Paper2.Certificates.DihedralSupport

/-- Expansion is proved by congruence, avoiding reduction of symbolic shifts. -/
theorem assemble_arithmetic (equal mixed : Nat × Nat) :
    assemble equal mixed = equal.1 + mixed.1 * 65536 +
      mixed.2 * 4294967296 + equal.2 * 281474976710656 := by
  have h16 : mixed.1 <<< 16 = mixed.1 * 65536 := Nat.shiftLeft_eq mixed.1 16
  have h32 : mixed.2 <<< 32 = mixed.2 * 4294967296 := Nat.shiftLeft_eq mixed.2 32
  have h48 : equal.2 <<< 48 = equal.2 * 281474976710656 := Nat.shiftLeft_eq equal.2 48
  exact congrArg₂ Nat.add
    (congrArg₂ Nat.add (congrArg (Nat.add equal.1) h16) h32) h48

set_option maxHeartbeats 0 in
/-- Four sixteen-bit blocks exhaust every six-bit support mask. -/
theorem assemble_slices (m : Nat) (hm : m < 18446744073709551616) :
    assemble (m % 65536, (m / 281474976710656) % 65536)
      ((m / 65536) % 65536, (m / 4294967296) % 65536) = m := by
  have harithmetic : m % 65536 + (m / 65536 % 65536) * 65536 +
      (m / 4294967296 % 65536) * 4294967296 +
      (m / 281474976710656 % 65536) * 281474976710656 = m := by
    have htop : m / 281474976710656 < 65536 :=
      (Nat.div_lt_iff_lt_mul (by decide)).mpr hm
    rw [Nat.mod_eq_of_lt htop]
    have h1 := Nat.mod_add_div (m / 65536) 65536
    rw [Nat.div_div_eq_div_mul] at h1
    have h2 := Nat.mod_add_div (m / 4294967296) 65536
    rw [Nat.div_div_eq_div_mul] at h2
    change m / 65536 % 65536 + 65536 * (m / 4294967296) = m / 65536 at h1
    change m / 4294967296 % 65536 + 65536 * (m / 281474976710656) =
      m / 4294967296 at h2
    calc
      _ = m % 65536 + 65536 * (m / 65536 % 65536 +
        65536 * (m / 4294967296 % 65536 + 65536 * (m / 281474976710656))) := by ring
      _ = m % 65536 + 65536 * (m / 65536 % 65536 + 65536 * (m / 4294967296)) := by rw [h2]
      _ = m % 65536 + 65536 * (m / 65536) := by rw [h1]
      _ = m := Nat.mod_add_div m 65536
  exact (assemble_arithmetic _ _).trans harithmetic


end Paper2.Certificates.DihedralSupport
