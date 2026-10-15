import Paper2.HeightOne.Dihedral.SixPortSupport

/-! The complete order-three union bound, derived from coefficient pencils on
all actual ordered-port sectors. The exceptional six-point case is discharged
by the tiny exact incidence certificate, including zero or proportional cards. -/
namespace Paper2.HeightOne.Dihedral.SixPortPencils
open Paper2.HeightOne SixPortSupport
noncomputable section
variable {K : Type} [Field K]

 def support (f : Signature K 6) : Finset SixPortSupport.Word6 := by
   classical
   exact Finset.univ.filter (fun x => f x ≠ 0)

 def first (f : Signature K 6) (p : Equiv.Perm (Fin 6)) (ξ : Bool) : Signature K 4 :=
   fun r => f (lift p ξ false r)
 def second (f : Signature K 6) (p : Equiv.Perm (Fin 6)) (ξ : Bool) : Signature K 4 :=
   fun r => f (lift p ξ true r)

 theorem joint_sector (f : Signature K 6) (p : Equiv.Perm (Fin 6)) (ξ : Bool) :
     jointSupport (first f p ξ) (second f p ξ) = sector (support f) p ξ := by
   classical
   ext r
   simp [mem_jointSupport,mem_sector,first,second,support,Bool.exists_bool,or_comm]

 theorem parity_extend (ξ b : Bool) (r : SixPortSupport.Word4) :
     parity (extend ξ b r) = (parity r + ξ.toNat) % 2 := by
   fin_cases r <;> cases ξ <;> cases b <;> decide +kernel

 theorem parity_lift (p : Equiv.Perm (Fin 6)) (ξ b : Bool) (r : SixPortSupport.Word4) :
     parity (lift p ξ b r) = (parity r + ξ.toNat) % 2 := by
   change Paper2.weight (fun i => extend ξ b r (p.symm i)) % 2 = _
   rw [weight_reindex]
   exact parity_extend ξ b r

 theorem sector_parity (f : Signature K 6) (hpar : HasParity f)
     (p : Equiv.Perm (Fin 6)) (ξ : Bool) :
     ∀ x ∈ sector (support f) p ξ, ∀ y ∈ sector (support f) p ξ,
       parity x = parity y := by
   classical
   intro x hx y hy
   obtain ⟨a,ha⟩ := (mem_sector _ p ξ x).mp hx
   obtain ⟨b,hb⟩ := (mem_sector _ p ξ y).mp hy
   have han : f (lift p ξ a x) ≠ 0 := by simpa [support] using ha
   have hbn : f (lift p ξ b y) ≠ 0 := by simpa [support] using hb
   have hh := hpar _ _ han hbn
   rw [parity_lift,parity_lift] at hh
   have hxlt : parity x < 2 := Nat.mod_lt _ (by decide)
   have hylt : parity y < 2 := Nat.mod_lt _ (by decide)
   cases ξ <;> simp only [Bool.toNat_false,Bool.toNat_true] at hh <;> omega

 theorem complete_at_six (f : Signature K 6) (S : Finset K)
     (hS : S.card = 3) (hsne : ∀ s ∈ S, s ≠ 0)
     (p : Equiv.Perm (Fin 6)) (ξ : Bool)
     (hcards : ∀ s ∈ S, (pencilSupport (first f p ξ) (second f p ξ) s).card ≤ 4)
     (hcard : (sector (support f) p ξ).card = 6) :
     CompleteSector (support f) p ξ := by
   classical
   intro r hr b
   have hU : (jointSupport (first f p ξ) (second f p ξ)).card = 6 := by
     rwa [joint_sector]
   have hrr : r ∈ jointSupport (first f p ξ) (second f p ξ) := by
     rwa [joint_sector]
   have hb := six_joint_both_slices (first f p ξ) (second f p ξ) S hS hsne hcards hU r hrr
   cases b
   · simpa [support,first] using hb.1
   · simpa [support,second] using hb.2

/-- The coefficient-level N=3 conclusion used by the six-port proof. Every
nonzero matching card has at most four support points and is complement closed;
these literal properties suffice, without any pencil classification premise. -/
theorem three_phase_union_card_le_four (f : Signature K 6) (hpar : HasParity f)
    (S : Finset K) (hS : S.card = 3) (hsne : ∀ s ∈ S, s ≠ 0)
    (hcards : ∀ p ξ s, s ∈ S →
      (pencilSupport (first f p ξ) (second f p ξ) s).card ≤ 4)
    (hcomp : ∀ p ξ s, s ∈ S → ∀ x ∈ pencilSupport (first f p ξ) (second f p ξ) s,
      complement x ∈ pencilSupport (first f p ξ) (second f p ξ) s)
    (ξ : Bool) :
    (jointSupport (first f (Equiv.refl _) ξ) (second f (Equiv.refl _) ξ)).card ≤ 4 := by
  classical
  have hbound : ∀ p η, (sector (support f) p η).card ≤ 6 := by
    intro p η
    rw [← joint_sector]
    exact joint_support_card_le_six (first f p η) (second f p η) S hS (hcards p η)
  have hcomplete : ∀ p η, (sector (support f) p η).card = 6 →
      CompleteSector (support f) p η := by
    intro p η hc
    exact complete_at_six f S hS hsne p η (hcards p η) hc
  have hc : ∀ x ∈ sector (support f) (Equiv.refl _) ξ,
      complement x ∈ sector (support f) (Equiv.refl _) ξ := by
    rw [← joint_sector]
    exact joint_support_complement_closed _ _ S (by omega) (hcomp _ ξ)
  have hne := first_sector_ne_six (support f) ξ hbound hcomplete hc
    (sector_parity f hpar (Equiv.refl _) ξ)
  have heven := complement_closed_card_even (by decide : 0 < 4) _ hc
  have hb := hbound (Equiv.refl _) ξ
  obtain ⟨k,hk⟩ := heven
  rw [joint_sector]
  omega

end
end Paper2.HeightOne.Dihedral.SixPortPencils
