import Counting.Algorithm.KarpLuby.DNF
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Fin

/-!
# Executable clause rank and unrank

Only unconstrained coordinates consume bits. The recursion visits each of the
explicit `n` variables, so isolated variables retain their full multiplicity.
-/

namespace Counting.Algorithm.KarpLuby.DNF

variable {n : ℕ}

def freeCount : {n : ℕ} → Clause n → ℕ
  | 0, _ => 0
  | _ + 1, c =>
    match c 0 with
    | none => freeCount (fun i => c i.succ) + 1
    | some _ => freeCount (fun i => c i.succ)

def clauseMass (c : Clause n) : ℕ := 2 ^ freeCount c

/-- Unrank in little-endian order on the unconstrained variables. -/
def sampleNat : {n : ℕ} → Clause n → ℕ → Assignment n
  | 0, _, _ => Fin.elim0
  | _ + 1, c, r =>
    match c 0 with
    | none => Fin.cons (r % 2 == 1) (sampleNat (fun i => c i.succ) (r / 2))
    | some b => Fin.cons b (sampleNat (fun i => c i.succ) r)

/-- Rank ignores constrained coordinates and packs the free coordinates. -/
def rankNat : {n : ℕ} → Clause n → Assignment n → ℕ
  | 0, _, _ => 0
  | _ + 1, c, a =>
    match c 0 with
    | none => (a 0).toNat + 2 * rankNat (fun i => c i.succ) (fun i => a i.succ)
    | some _ => rankNat (fun i => c i.succ) (fun i => a i.succ)

theorem freeCount_le (c : Clause n) : freeCount c ≤ n := by
  induction n with
  | zero => simp [freeCount]
  | succ n ih =>
    cases hc : c 0 <;> simp only [freeCount, hc]
    · exact Nat.add_le_add_right (ih _) 1
    · exact (ih _).trans (Nat.le_succ _)

theorem clauseMass_pos (c : Clause n) : 0 < clauseMass c := by
  exact pow_pos (by decide) _

theorem clauseMass_le (c : Clause n) : clauseMass c ≤ 2 ^ n := by
  exact Nat.pow_le_pow_right (by decide) (freeCount_le c)

theorem sampleNat_satisfies (c : Clause n) (r : ℕ) : Satisfies c (sampleNat c r) := by
  induction n generalizing r with
  | zero => simp [Satisfies]
  | succ n ih =>
    rw [satisfies_succ]
    cases hc : c 0 <;> simp [sampleNat, hc, ih]

theorem rankNat_lt (c : Clause n) (a : Assignment n) : rankNat c a < clauseMass c := by
  induction n with
  | zero => simp [rankNat, clauseMass, freeCount]
  | succ n ih =>
    have ht := ih (fun i => c i.succ) (fun i => a i.succ)
    cases hc : c 0 with
    | none =>
      simp only [rankNat, hc, clauseMass, freeCount, pow_succ] at *
      have hb : (a 0).toNat < 2 := by cases a 0 <;> decide
      omega
    | some b => simpa only [rankNat, hc, clauseMass, freeCount] using ht

theorem sampleNat_rankNat (c : Clause n) (a : Assignment n) (ha : Satisfies c a) :
    sampleNat c (rankNat c a) = a := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨h0, ht⟩ := (satisfies_succ c a).mp ha
    have hit := ih (fun i => c i.succ) (fun i => a i.succ) ht
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · cases hc : c 0 with
      | none => cases hb : a 0 <;> simp [sampleNat, rankNat, hc, hb]
      | some b => simpa [sampleNat, rankNat, hc] using (h0 b hc).symm
    · cases hc : c 0 with
      | none =>
        have hb : (a 0).toNat < 2 := by cases a 0 <;> decide
        have hd : ((a 0).toNat + 2 * rankNat (fun i => c i.succ)
            (fun i => a i.succ)) / 2 = rankNat (fun i => c i.succ)
            (fun i => a i.succ) := by omega
        simpa [sampleNat, rankNat, hc, hd] using congrFun hit j
      | some b => simpa [sampleNat, rankNat, hc] using congrFun hit j

theorem rankNat_sampleNat (c : Clause n) (r : ℕ) (hr : r < clauseMass c) :
    rankNat c (sampleNat c r) = r := by
  induction n generalizing r with
  | zero => simp [clauseMass, freeCount] at hr; simp [rankNat, hr]
  | succ n ih =>
    cases hc : c 0 with
    | none =>
      have ht : r / 2 < clauseMass (fun i => c i.succ) := by
        simp only [clauseMass, freeCount, hc, pow_succ] at hr ⊢
        omega
      have hit := ih (fun i => c i.succ) (r / 2) ht
      have hb : (decide (r % 2 = 1)).toNat = r % 2 := by
        have hm := Nat.mod_lt r (by decide : 0 < 2)
        interval_cases r % 2 <;> simp
      simp only [sampleNat, hc, rankNat, Fin.cons_zero, Fin.cons_succ]
      rw [hit]
      change (decide (r % 2 = 1)).toNat + 2 * (r / 2) = r
      rw [hb]
      omega
    | some b =>
      have ht : r < clauseMass (fun i => c i.succ) := by
        simpa only [clauseMass, freeCount, hc] using hr
      simpa only [sampleNat, hc, rankNat, Fin.cons_succ] using
        ih (fun i => c i.succ) r ht

/-- Constructive finite indexing, with both inverse laws checked. -/
def sampleEquiv (c : Clause n) : Fin (clauseMass c) ≃ {a : Assignment n // Satisfies c a} where
  toFun r := ⟨sampleNat c r.val, sampleNat_satisfies c r.val⟩
  invFun a := ⟨rankNat c a.val, rankNat_lt c a.val⟩
  left_inv r := Fin.ext (rankNat_sampleNat c r.val r.isLt)
  right_inv a := Subtype.ext (sampleNat_rankNat c a.val a.property)

theorem card_satisfies (c : Clause n) :
    Fintype.card {a : Assignment n // Satisfies c a} = 2 ^ freeCount c := by
  exact (Fintype.card_congr (sampleEquiv c)).symm.trans (Fintype.card_fin _)

theorem sampleNat_injective (c : Clause n) :
    Function.Injective (fun r : Fin (clauseMass c) => sampleNat c r.val) := by
  intro r s hrs
  exact Fin.ext ((rankNat_sampleNat c r.val r.isLt).symm.trans
    ((congrArg (rankNat c) hrs).trans (rankNat_sampleNat c s.val s.isLt)))

theorem exists_sampleNat (c : Clause n) (a : Assignment n) (ha : Satisfies c a) :
    ∃ r < clauseMass c, sampleNat c r = a :=
  ⟨rankNat c a, rankNat_lt c a, sampleNat_rankNat c a ha⟩

end Counting.Algorithm.KarpLuby.DNF
