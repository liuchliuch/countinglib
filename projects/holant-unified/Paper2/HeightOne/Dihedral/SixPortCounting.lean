import Paper2.HeightOne.Dihedral.PencilCounting

/-! The order-three support bound uses only the actual phase-pencil supports.
At the only possible exceptional cardinality, six, every coordinate cancels at
one phase, and consequently occurs in both source slices. This turns the
remaining support exclusion into a finite Boolean incidence statement. -/
namespace Paper2.HeightOne.Dihedral
open scoped BigOperators
noncomputable section
variable {X K : Type*} [Fintype X] [Field K]
local instance : DecidableEq K := Classical.decEq K

 theorem joint_support_card_le_six (A B : X → K) (S : Finset K)
    (hS : S.card = 3) (hcards : ∀ s ∈ S, (pencilSupport A B s).card ≤ 4) :
    (jointSupport A B).card ≤ 6 := by
  have h := pencil_support_double_count A B S
  have hb : (∑ s ∈ S, (pencilSupport A B s).card) ≤ S.card * 4 := by
    calc
      _ ≤ ∑ _s ∈ S, 4 := Finset.sum_le_sum hcards
      _ = _ := by simp
  rw [hS] at h hb
  omega

 theorem pencil_incidence_swap (A B : X → K) (S : Finset K) :
    (∑ x ∈ jointSupport A B, (S.filter (fun s => A x - s * B x ≠ 0)).card) =
      ∑ s ∈ S, (pencilSupport A B s).card := by
  classical
  have hswap := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := jointSupport A B) (t := S) (fun (x : X) (s : K) => A x - s * B x ≠ 0)
  have hfilter : ∀ s, ((jointSupport A B).filter (fun x => A x - s * B x ≠ 0)) =
      pencilSupport A B s := by
    intro s
    ext x
    simp only [Finset.mem_filter,mem_jointSupport,mem_pencilSupport]
    constructor
    · exact And.right
    · intro hx
      exact ⟨(mem_jointSupport A B x).mp (pencilSupport_subset A B s
        ((mem_pencilSupport A B s x).mpr hx)),hx⟩
  simpa only [Finset.bipartiteAbove,Finset.bipartiteBelow,hfilter] using hswap

/-- Equality in the three-phase incidence bound forces a cancellation at
 every joint-supported coordinate. No phase ratio or coefficient orbit is
 assumed. -/
theorem six_joint_coordinate_cancels (A B : X → K) (S : Finset K)
    (hS : S.card = 3) (hcards : ∀ s ∈ S, (pencilSupport A B s).card ≤ 4)
    (hU : (jointSupport A B).card = 6) (x : X) (hx : x ∈ jointSupport A B) :
    ∃ s ∈ S, A x - s * B x = 0 := by
  classical
  by_contra hn
  have hn' : ∀ s ∈ S, A x - s * B x ≠ 0 := by simpa using hn
  have hc : (S.filter (fun s => A x - s * B x ≠ 0)).card = 3 := by
    rw [Finset.filter_eq_self.mpr hn',hS]
  have hstrict : (∑ _y ∈ jointSupport A B, (2 : ℕ)) <
      ∑ y ∈ jointSupport A B, (S.filter (fun s => A y - s * B y ≠ 0)).card := by
    apply Finset.sum_lt_sum
    · intro y hy
      have hs := surviving_phases_card A B S y hy
      simpa [hS] using hs
    · exact ⟨x,hx,by omega⟩
  have hbound : (∑ s ∈ S, (pencilSupport A B s).card) ≤ 12 := by
    calc
      _ ≤ ∑ _s ∈ S, 4 := Finset.sum_le_sum hcards
      _ = 12 := by simp [hS]
  rw [pencil_incidence_swap] at hstrict
  simp [hU] at hstrict
  omega

/-- At union size six both literal lifts are nonzero. This is the only
extra support rule needed for the order-three finite Boolean exclusion. -/
theorem six_joint_both_slices (A B : X → K) (S : Finset K)
    (hS : S.card = 3) (hsne : ∀ s ∈ S, s ≠ 0)
    (hcards : ∀ s ∈ S, (pencilSupport A B s).card ≤ 4)
    (hU : (jointSupport A B).card = 6) (x : X) (hx : x ∈ jointSupport A B) :
    A x ≠ 0 ∧ B x ≠ 0 := by
  obtain ⟨s,hs,hcancel⟩ := six_joint_coordinate_cancels A B S hS hcards hU x hx
  have he : A x = s * B x := sub_eq_zero.mp hcancel
  have hb : B x ≠ 0 := by
    intro hb
    have ha : A x = 0 := by simpa [hb] using he
    rcases (mem_jointSupport A B x).mp hx with h | h
    · exact h ha
    · exact h hb
  exact ⟨by rw [he]; exact mul_ne_zero (hsne s hs) hb,hb⟩

end
end Paper2.HeightOne.Dihedral
