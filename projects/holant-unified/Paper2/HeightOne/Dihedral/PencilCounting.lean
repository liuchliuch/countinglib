import Paper2.Signature
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

/-! The support double-count in the six-port odd-dihedral proof. These results
use the actual two-slice pencil A-sB over a field.  No matching-pencil rigidity
or finite-certificate classification is assumed. -/
namespace Paper2.HeightOne.Dihedral
open scoped BigOperators
noncomputable section

variable {X K : Type*} [Fintype X] [Field K]
local instance : DecidableEq K := Classical.decEq K

def pencilSupport (A B : X → K) (s : K) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => A x - s * B x ≠ 0)

def jointSupport (A B : X → K) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => A x ≠ 0 ∨ B x ≠ 0)

@[simp] theorem mem_pencilSupport (A B : X → K) (s : K) (x : X) :
    x ∈ pencilSupport A B s ↔ A x - s * B x ≠ 0 := by
  classical
  simp [pencilSupport]

@[simp] theorem mem_jointSupport (A B : X → K) (x : X) :
    x ∈ jointSupport A B ↔ A x ≠ 0 ∨ B x ≠ 0 := by
  classical
  simp [jointSupport]

theorem pencilSupport_subset (A B : X → K) (s : K) :
    pencilSupport A B s ⊆ jointSupport A B := by
  intro x hx
  rw [mem_pencilSupport] at hx
  rw [mem_jointSupport]
  by_contra h
  push_neg at h
  exact hx (by rw [h.1, h.2]; ring)

/-- At most one distinct phase can cancel a coordinate belonging to either
slice.  The assertion also covers a zero value in exactly one of the slices. -/
theorem cancelled_phases_card_le_one (A B : X → K) (S : Finset K) (x : X)
    (hx : x ∈ jointSupport A B) :
    (S.filter (fun s => A x - s * B x = 0)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro s hs t ht
  have hs' := sub_eq_zero.mp (Finset.mem_filter.mp hs).2
  have ht' := sub_eq_zero.mp (Finset.mem_filter.mp ht).2
  have hB : B x ≠ 0 := by
    intro hB
    have hA : A x = 0 := by simpa only [hB, mul_zero] using hs'
    rcases (mem_jointSupport A B x).mp hx with ha | hb
    · exact ha hA
    · exact hb hB
  exact mul_right_cancel₀ hB (hs'.symm.trans ht')

theorem surviving_phases_card (A B : X → K) (S : Finset K) (x : X)
    (hx : x ∈ jointSupport A B) :
    S.card - 1 ≤ (S.filter (fun s => A x - s * B x ≠ 0)).card := by
  classical
  have hzero := cancelled_phases_card_le_one A B S x hx
  have hsum : (S.filter (fun s => A x - s * B x = 0)).card +
      (S.filter (fun s => A x - s * B x ≠ 0)).card = S.card :=
    Finset.card_filter_add_card_filter_not (s := S) (fun s => A x - s * B x = 0)
  omega

/-- The displayed inequality (N-1)|U| ≤ sum_s |supp(A-sB)| in the source. -/
theorem pencil_support_double_count (A B : X → K) (S : Finset K) :
    (S.card - 1) * (jointSupport A B).card ≤ ∑ s ∈ S, (pencilSupport A B s).card := by
  classical
  have hswap := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := jointSupport A B) (t := S) (fun (x : X) (s : K) => A x - s * B x ≠ 0)
  have hfilter : ∀ s, ((jointSupport A B).filter (fun x => A x - s * B x ≠ 0)) =
      pencilSupport A B s := by
    intro s
    ext x
    simp only [Finset.mem_filter, mem_jointSupport, mem_pencilSupport]
    constructor
    · exact And.right
    · intro hx
      exact ⟨(mem_jointSupport A B x).mp (pencilSupport_subset A B s ((mem_pencilSupport A B s x).mpr hx)), hx⟩
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow, hfilter] at hswap
  calc
    _ = ∑ _x ∈ jointSupport A B, (S.card - 1) := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ jointSupport A B, (S.filter (fun s => A x - s * B x ≠ 0)).card :=
      Finset.sum_le_sum (fun x hx => surviving_phases_card A B S x hx)
    _ = _ := hswap

theorem joint_mem_iff_pencil_mem (A B : X → K) (S : Finset K) (hS : 2 ≤ S.card) (x : X) :
    x ∈ jointSupport A B ↔ ∃ s ∈ S, x ∈ pencilSupport A B s := by
  classical
  constructor
  · intro hx
    have hc := surviving_phases_card A B S x hx
    obtain ⟨s, hs⟩ := Finset.card_pos.mp (show 0 < (S.filter (fun s => A x - s * B x ≠ 0)).card by omega)
    exact ⟨s, (Finset.mem_filter.mp hs).1, (mem_pencilSupport A B s x).mpr (Finset.mem_filter.mp hs).2⟩
  · rintro ⟨s, _, hs⟩
    exact pencilSupport_subset A B s hs

/-- If every member of the pencil has at most four supported coordinates,
five or more phases leave at most five coordinates in the union. -/
theorem joint_support_card_le_five (A B : X → K) (S : Finset K) (hS : 5 ≤ S.card)
    (hcards : ∀ s ∈ S, (pencilSupport A B s).card ≤ 4) :
    (jointSupport A B).card ≤ 5 := by
  have h := pencil_support_double_count A B S
  have hbound : (∑ s ∈ S, (pencilSupport A B s).card) ≤ S.card * 4 := by
    calc
      _ ≤ ∑ _s ∈ S, 4 := Finset.sum_le_sum hcards
      _ = _ := by simp
  have hn : S.card - 1 + 1 = S.card := Nat.sub_add_cancel (by omega)
  by_contra hlarge
  have hlarge' : 6 ≤ (jointSupport A B).card := by omega
  have hmul := Nat.mul_le_mul_left (S.card - 1) hlarge'
  nlinarith

/-- Complement pairs give an actual even support cardinality. This records the
source's parity improvement from at most five points to at most four. -/
theorem complement_closed_card_even {n : ℕ} (hn : 0 < n)
    (U : Finset (Fin n → Bool))
    (hcomp : ∀ x ∈ U, (fun i => !(x i)) ∈ U) : Even U.card := by
  classical
  let p : Fin n := ⟨0, hn⟩
  have hcards : (U.filter (fun x => x p = false)).card = (U.filter (fun x => x p = true)).card := by
    apply Finset.card_bij' (fun x _ => fun i => !(x i)) (fun x _ => fun i => !(x i))
    · intro x hx
      obtain ⟨hU, hp⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hcomp x hU, by simp [hp]⟩
    · intro x hx
      obtain ⟨hU, hp⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hcomp x hU, by simp [hp]⟩
    · intro x _
      simp
    · intro x _
      simp
  have hsum : (U.filter (fun x => x p = false)).card +
      (U.filter (fun x => x p = true)).card = U.card := by
    simpa only [Bool.not_eq_false] using
      Finset.card_filter_add_card_filter_not (s := U) (fun x => x p = false)
  exact ⟨(U.filter (fun x => x p = false)).card, by omega⟩

theorem joint_support_complement_closed {n : ℕ} (A B : Signature K n) (S : Finset K)
    (hS : 2 ≤ S.card)
    (hcomp : ∀ s ∈ S, ∀ x ∈ pencilSupport A B s, (fun i => !(x i)) ∈ pencilSupport A B s) :
    ∀ x ∈ jointSupport A B, (fun i => !(x i)) ∈ jointSupport A B := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (joint_mem_iff_pencil_mem A B S hS x).mp hx
  exact pencilSupport_subset A B s (hcomp s hs x hx)

/-- The N≥5 half of the six-port support argument, including zero pencil
members and the actual complement-pair improvement. -/
theorem six_port_pencil_union_card_le_four (A B : Signature K 4) (S : Finset K)
    (hS : 5 ≤ S.card) (hcards : ∀ s ∈ S, (pencilSupport A B s).card ≤ 4)
    (hcomp : ∀ s ∈ S, ∀ x ∈ pencilSupport A B s, (fun i => !(x i)) ∈ pencilSupport A B s) :
    (jointSupport A B).card ≤ 4 := by
  have hfive := joint_support_card_le_five A B S hS hcards
  have heven := complement_closed_card_even (by decide : 0 < 4) (jointSupport A B)
    (joint_support_complement_closed A B S (by omega) hcomp)
  obtain ⟨k, hk⟩ := heven
  omega

end
end Paper2.HeightOne.Dihedral

