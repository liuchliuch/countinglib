import Paper2.ReedMuller
import Mathlib.Tactic.LinearCombination

/-! Finite spanning-tree witnesses for Proposition A.10. The integer masks are
untrusted data: the universal validity and coverage theorems below are checked
by reduction in Lean's kernel. Bits index ports 000,...,111. -/
namespace Paper2.Certificates.Q8
open ReedMuller

def fromMask (m : ℕ) : Word := fun t => m.testBit t.val

def swap (x : Word) (p q : Fin 8) : Word :=
  fun t => if t = p then false else if t = q then true else x t

def direction (p q : Fin 8) : Fin 3 → Bool :=
  fun j => Bool.xor (point p j) (point q j)

/-- A nonplane-preserving swap with zero right-hand side in Q8.19a. -/
def BadSwap (x y : Word) (p q : Fin 8) : Prop :=
  weight x = 4 ∧ x p = true ∧ x q = false ∧ y = swap x p q ∧
  supportXor x ≠ (fun _ => false) ∧ supportXor x ≠ direction p q

instance (x y : Word) (p q : Fin 8) : Decidable (BadSwap x y p q) :=
  inferInstanceAs (Decidable (weight x = 4 ∧ x p = true ∧ x q = false ∧
    y = swap x p q ∧ supportXor x ≠ (fun _ => false) ∧
      supportXor x ≠ direction p q))

def nonplaneMasks : Fin 56 → ℕ :=
  ![23, 30, 54, 86, 29, 53, 149, 27, 83, 147, 39, 71, 135, 92, 156, 58, 154, 46, 78, 142, 116, 180, 114, 178, 166, 212, 210, 198, 57, 89, 45, 77, 141, 113, 177, 101, 209, 197, 43, 75, 139, 99, 163, 120, 216, 108, 184, 172, 106, 202, 228, 226, 169, 201, 225, 232]

def nonplane (i : Fin 56) : Word := fromMask (nonplaneMasks i)

/-- Parent index and the removed/inserted port for each nonroot vertex. -/
def tree : Fin 56 → Fin 56 × Fin 8 × Fin 8 :=
  ![(0, 0, 0), (0, 0, 3), (0, 0, 5), (0, 0, 6), (0, 1, 3), (0, 1, 5), (0, 1, 7), (0, 2, 3), (0, 2, 6), (0, 2, 7), (0, 4, 5), (0, 4, 6), (0, 4, 7), (1, 1, 6), (1, 1, 7), (1, 2, 5), (1, 2, 7), (1, 4, 5), (1, 4, 6), (1, 4, 7), (2, 1, 6), (2, 1, 7), (2, 2, 6), (2, 2, 7), (2, 4, 7), (3, 1, 7), (3, 2, 7), (3, 4, 7), (4, 2, 5), (4, 2, 6), (4, 4, 5), (4, 4, 6), (4, 4, 7), (5, 2, 6), (5, 2, 7), (5, 4, 6), (6, 2, 6), (6, 4, 6), (7, 4, 5), (7, 4, 6), (7, 4, 7), (8, 4, 5), (9, 4, 5), (13, 2, 5), (13, 2, 7), (13, 4, 5), (14, 2, 5), (14, 4, 5), (15, 4, 6), (16, 4, 6), (20, 4, 7), (22, 4, 7), (28, 4, 7), (29, 4, 7), (33, 4, 7), (43, 4, 7)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tree_valid (i : Fin 56) (hi : i.val ≠ 0) :
    (tree i).1.val < i.val ∧
      BadSwap (nonplane (tree i).1) (nonplane i) (tree i).2.1 (tree i).2.2 := by
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nonplane_coverage (x : Word) (hw : weight x = 4)
    (hx : supportXor x ≠ (fun _ => false)) : ∃ i : Fin 56, x = nonplane i := by
  revert x
  decide +kernel

/-- The exact odd cycle 0124--0125--0245--0124 printed as Q8.20. -/
theorem odd_triangle :
    BadSwap (fromMask 23) (fromMask 39) 4 5 ∧
    BadSwap (fromMask 39) (fromMask 53) 1 4 ∧
    BadSwap (fromMask 53) (fromMask 23) 5 1 := by
  decide +kernel

/-- Q8.19a kills every nonplane coefficient. The only scalar requirement is
that two is nonzero and there are no zero divisors, so this applies over ℂ. -/
theorem nonplane_zero_of_bad_swaps {K : Type*} [CommRing K]
    [NoZeroDivisors K] [CharZero K] (c : Word → K)
    (hs : ∀ x y p q, BadSwap x y p q → c x + c y = 0)
    (x : Word) (hw : weight x = 4)
    (hx : supportXor x ≠ (fun _ => false)) : c x = 0 := by
  have h01 := hs _ _ _ _ odd_triangle.1
  have h12 := hs _ _ _ _ odd_triangle.2.1
  have h20 := hs _ _ _ _ odd_triangle.2.2
  have hz : (2 : K) * c (fromMask 23) = 0 := by
    linear_combination h01 - h12 + h20
  have hroot : c (nonplane 0) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (by norm_num)
  have all_zero : ∀ n (hn : n < 56), c (nonplane ⟨n, hn⟩) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hn0 : n = 0
      · subst n
        exact hroot
      · have ht := tree_valid ⟨n, hn⟩ hn0
        have hp := ih (tree ⟨n, hn⟩).1.val ht.1 (tree ⟨n, hn⟩).1.isLt
        have he := hs _ _ _ _ ht.2
        rw [hp, zero_add] at he
        exact he
  obtain ⟨i, rfl⟩ := nonplane_coverage x hw hx
  exact all_zero i.val i.isLt


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exchanging one inside/outside point of an affine plane gives a nonplane. -/
theorem plane_swap_nonplane (x : Word) (p q : Fin 8)
    (hw : weight x = 4) (hx : supportXor x = (fun _ => false))
    (hp : x p = true) (hq : x q = false) :
    weight (swap x p q) = 4 ∧ supportXor (swap x p q) ≠ (fun _ => false) := by
  revert x p q
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every affine plane and the reference plane 0123 have a common crossing pair.
This is a directly checked finite incidence-connectivity witness. -/
theorem common_reference_pair (x : Word) (hw : weight x = 4)
    (hx : supportXor x = (fun _ => false)) :
    ∃ p q : Fin 8, x p = true ∧ x q = false ∧ fromMask 15 p ≠ fromMask 15 q := by
  revert x
  decide +kernel

/-- Q8.19a. Symmetry of `lam` separately encodes its unordered pair domain. -/
def SwapSystem {K : Type*} [Add K] [Zero K] (c : Word → K)
    (lam : Fin 8 → Fin 8 → K) : Prop :=
  ∀ x p q, weight x = 4 → x p = true → x q = false →
    c x + c (swap x p q) =
      if supportXor x = (fun _ => false) ∨ supportXor x = direction p q
      then lam p q else 0

/-- The full coefficient conclusion of Proposition A.10 / Theorem A.11.
This is a theorem about the actual 70 weight-four Boolean tensor entries,
not an assertion of the external Python verifier's success. -/
theorem canonical_support {K : Type*} [CommRing K]
    [NoZeroDivisors K] [CharZero K] (c : Word → K)
    (lam : Fin 8 → Fin 8 → K) (hs : SwapSystem c lam)
    (hsym : ∀ p q, lam p q = lam q p)
    (hnz : ∀ p q, p ≠ q → lam p q ≠ 0) :
    ∃ k : K, k ≠ 0 ∧ ∀ x : Word, weight x = 4 →
      c x = if supportXor x = (fun _ => false) then k else 0 := by
  have hbad : ∀ x, weight x = 4 → supportXor x ≠ (fun _ => false) → c x = 0 := by
    intro x hw hx
    apply nonplane_zero_of_bad_swaps c _ x hw hx
    intro u v p q h
    obtain ⟨hu, hp, hq, rfl, hx, hd⟩ := h
    simpa [hx, hd] using hs u p q hu hp hq
  have hplane : ∀ x p q, weight x = 4 → supportXor x = (fun _ => false) →
      x p = true → x q = false → c x = lam p q := by
    intro x p q hw hx hp hq
    obtain ⟨hsw, hsn⟩ := plane_swap_nonplane x p q hw hx hp hq
    have he := hs x p q hw hp hq
    rw [hbad _ hsw hsn, add_zero] at he
    simpa [hx] using he
  have hweight : weight (fromMask 15) = 4 := by decide +kernel
  have hxor : supportXor (fromMask 15) = (fun _ => false) := by decide +kernel
  have href : c (fromMask 15) = lam 0 4 :=
    hplane _ _ _ hweight hxor (by decide) (by decide)
  refine ⟨c (fromMask 15), ?_, ?_⟩
  · rw [href]
    exact hnz 0 4 (by decide)
  · intro x hw
    split_ifs with hx
    · obtain ⟨p, q, hp, hq, hc⟩ := common_reference_pair x hw hx
      have hxp := hplane x p q hw hx hp hq
      have hrf : c (fromMask 15) = lam p q := by
        cases hrp : fromMask 15 p <;> cases hrq : fromMask 15 q
        · exact False.elim (hc (hrp.trans hrq.symm))
        · rw [hsym p q]
          exact hplane _ q p hweight hxor hrq hrp
        · exact hplane _ p q hweight hxor hrp hrq
        · exact False.elim (hc (hrp.trans hrq.symm))
      exact hxp.trans hrf.symm
    · exact hbad x hw hx


/-- The tensor-level form: an EO signature satisfying Q8.19a is a nonzero
scalar multiple of the central Reed--Muller signature. -/
theorem scalar_central_of_swap_system {K : Type*} [CommRing K]
    [NoZeroDivisors K] [CharZero K] (c : Signature K 8)
    (lam : Fin 8 → Fin 8 → K) (hs : SwapSystem c lam)
    (hsym : ∀ p q, lam p q = lam q p)
    (hnz : ∀ p q, p ≠ q → lam p q ≠ 0)
    (heo : ∀ x, weight x ≠ 4 → c x = 0) :
    ∃ k : K, k ≠ 0 ∧ c = fun x => k * central x := by
  obtain ⟨k, hk, hc⟩ := canonical_support c lam hs hsym hnz
  refine ⟨k, hk, ?_⟩
  funext x
  by_cases hw : weight x = 4
  · have hcentral : IsCentral x ↔ supportXor x = (fun _ => false) := by
      simpa only [hw, true_and] using central_iff_plane x
    simpa [central, hcentral, mul_ite] using hc x hw
  · rw [heo x hw]
    simp [central, IsCentral, hw]

end Paper2.Certificates.Q8
