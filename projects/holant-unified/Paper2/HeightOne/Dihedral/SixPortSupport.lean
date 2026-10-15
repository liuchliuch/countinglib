import Paper2.HeightOne.Dihedral.SixPortCounting
import Paper2.HeightOne.Parity

/-! A small exact incidence certificate replacing the order-three projective
pencil enumeration for matching-product cards. Six supported residual words
must be a parity class with one complementary pair deleted. Their two lifts
force a second six-point projection to have both lifts as well; that completed
support has an eight-point projection. All concrete Boolean geometry below is
proved by kernel reduction over the sixteen possible omitted words. -/
namespace Paper2.HeightOne.Dihedral.SixPortSupport
open Paper2.HeightOne
noncomputable section
set_option maxHeartbeats 0
abbrev Word4 := Fin 4 → Bool
abbrev Word6 := Fin 6 → Bool

 def complement (x : Word4) : Word4 := fun i => !(x i)
 def residual (x : Word6) : Word4 := fun i => x i.succ.succ
 def extend (ξ b : Bool) (r : Word4) : Word6 := Fin.cons b (Fin.cons (Bool.xor b ξ) r)
 def lift (p : Equiv.Perm (Fin 6)) (ξ b : Bool) (r : Word4) : Word6 :=
   fun i => extend ξ b r (p.symm i)

 def sector (S : Finset Word6) (p : Equiv.Perm (Fin 6)) (ξ : Bool) : Finset Word4 := by
   classical
   exact Finset.univ.filter (fun r => ∃ b : Bool, lift p ξ b r ∈ S)

 def CompleteSector (S : Finset Word6) (p : Equiv.Perm (Fin 6)) (ξ : Bool) : Prop :=
   ∀ r ∈ sector S p ξ, ∀ b, lift p ξ b r ∈ S

 def completion (S : Finset Word6) (p : Equiv.Perm (Fin 6)) : Finset Word6 := by
   classical
   exact Finset.univ.filter (fun x =>
     residual (x ∘ p) ∈ sector S p (Bool.xor (x (p 0)) (x (p 1))))

 def parityClass (a : Word4) : Finset Word4 := by
   classical
   exact Finset.univ.filter (fun r => parity r = parity a)

 def threeBlocks (a : Word4) : Finset Word4 := by
   classical
   exact (parityClass a).erase a |>.erase (complement a)

 def seed (a : Word4) (ξ : Bool) : Finset Word6 := by
   classical
   exact Finset.univ.filter (fun x =>
     Bool.xor (x 0) (x 1) = ξ ∧ residual x ∈ threeBlocks a)

 def pair02 : Equiv.Perm (Fin 6) where
   toFun := ![0,2,1,3,4,5]
   invFun := ![0,2,1,3,4,5]
   left_inv := by decide +kernel
   right_inv := by decide +kernel

 def pair03 : Equiv.Perm (Fin 6) where
   toFun := ![0,3,1,2,4,5]
   invFun := ![0,2,3,1,4,5]
   left_inv := by decide +kernel
   right_inv := by decide +kernel

 lemma complement_complement (a : Word4) : complement (complement a) = a := by
   funext i
   simp [complement]

 lemma complement_ne (a : Word4) : complement a ≠ a := by
   intro h
   have hh := congrFun h 0
   cases ha : a 0 <;> simp [complement,ha] at hh

 lemma parity_complement (a : Word4) : parity (complement a) = parity a := by
   fin_cases a <;> decide +kernel

 lemma parityClass_card (a : Word4) : (parityClass a).card = 8 := by
   fin_cases a <;> decide +kernel

 lemma threeBlocks_card (a : Word4) : (threeBlocks a).card = 6 := by
   fin_cases a <;> decide +kernel

 /-- The first cross-pair projection has exactly six words in both sectors. -/
 theorem seed_pair02_card (a : Word4) (ξ η : Bool) :
     (sector (seed a ξ) pair02 η).card = 6 := by
   fin_cases a <;> cases ξ <;> cases η <;> decide +kernel

 /-- Filling those two six-point sectors forces eight words on the next pair. -/
 theorem completion_pair03_card (a : Word4) (ξ : Bool) :
     (sector (completion (seed a ξ) pair02) pair03 false).card = 8 := by
   fin_cases a <;> cases ξ <;> decide +kernel

 lemma mem_sector (S : Finset Word6) (p : Equiv.Perm (Fin 6)) (ξ : Bool) (r : Word4) :
     r ∈ sector S p ξ ↔ ∃ b : Bool, lift p ξ b r ∈ S := by
   classical
   simp [sector]

 lemma sector_mono {S T : Finset Word6} (h : S ⊆ T)
     (p : Equiv.Perm (Fin 6)) (ξ : Bool) : sector S p ξ ⊆ sector T p ξ := by
   intro r hr
   obtain ⟨b,hb⟩ := (mem_sector S p ξ r).mp hr
   exact (mem_sector T p ξ r).mpr ⟨b,h hb⟩

 lemma completion_mono {S T : Finset Word6} (h : S ⊆ T)
     (p : Equiv.Perm (Fin 6)) : completion S p ⊆ completion T p := by
   classical
   intro x hx
   simp only [completion,Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
   exact sector_mono h p _ hx

 lemma lift_residual (p : Equiv.Perm (Fin 6)) (x : Word6) :
     lift p (Bool.xor (x (p 0)) (x (p 1))) (x (p 0)) (residual (x ∘ p)) = x := by
   have h : ∀ y : Word6, extend (Bool.xor (y 0) (y 1)) (y 0) (residual y) = y := by
     intro y
     funext k
     refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => rfl) j) k
     · rfl
     · simp [extend,Bool.xor_assoc]
   funext i
   have hh := congrFun (h (x ∘ p)) (p.symm i)
   simpa only [lift,Function.comp_apply,Equiv.apply_symm_apply] using hh

 lemma completion_subset (S : Finset Word6) (p : Equiv.Perm (Fin 6))
     (h : ∀ ξ, CompleteSector S p ξ) : completion S p ⊆ S := by
   classical
   intro x hx
   have hr : residual (x ∘ p) ∈ sector S p (Bool.xor (x (p 0)) (x (p 1))) := by
     simpa [completion] using hx
   have hh := h _ _ hr (x (p 0))
   rwa [lift_residual] at hh

 /-- A complement-closed six-point union with one parity is precisely one
 of the sixteen explicit three-block sets used by the incidence certificate. -/
 theorem six_union_threeBlocks (U : Finset Word4) (hcard : U.card = 6)
     (hcomp : ∀ x ∈ U, complement x ∈ U)
     (hpar : ∀ x ∈ U, ∀ y ∈ U, parity x = parity y) :
     ∃ a : Word4, U = threeBlocks a := by
   classical
   obtain ⟨r,hr⟩ := Finset.card_pos.mp (show 0 < U.card by omega)
   have hsub : U ⊆ parityClass r := by
     intro x hx
     simp only [parityClass,Finset.mem_filter,Finset.mem_univ,true_and]
     exact hpar x hx r hr
   obtain ⟨a,ha,han⟩ := Finset.exists_mem_notMem_of_card_lt_card
     (show U.card < (parityClass r).card by rw [hcard,parityClass_card]; omega)
   have hpa : parity a = parity r := by simpa [parityClass] using ha
   have hcan : complement a ∉ U := by
     intro hc
     have hh := hcomp _ hc
     rw [complement_complement] at hh
     exact han hh
   have hU : U ⊆ threeBlocks a := by
     intro x hx
     simp only [threeBlocks,Finset.mem_erase,parityClass,Finset.mem_filter,
       Finset.mem_univ,true_and]
     exact ⟨fun he => hcan (he ▸ hx),fun he => han (he ▸ hx),(hpar x hx r hr).trans hpa.symm⟩
   exact ⟨a,Finset.eq_of_subset_of_card_le hU (by rw [hcard,threeBlocks_card])⟩

 lemma seed_subset (S : Finset Word6) (a : Word4) (ξ : Bool)
     (hU : sector S (Equiv.refl _) ξ = threeBlocks a)
     (hcomplete : CompleteSector S (Equiv.refl _) ξ) : seed a ξ ⊆ S := by
   classical
   intro x hx
   obtain ⟨hxor,hr⟩ : Bool.xor (x 0) (x 1) = ξ ∧ residual x ∈ threeBlocks a := by
     simpa [seed] using hx
   have hh := hcomplete (residual x) (by simpa [hU] using hr) (x 0)
   have he : lift (Equiv.refl (Fin 6)) ξ (x 0) (residual x) = x := by
     rw [← hxor]
     simpa using lift_residual (Equiv.refl (Fin 6)) x
   rwa [he] at hh

 /-- Six-word sectors cannot occur anywhere in a support satisfying the
 three-phase bounds and their equality condition. This is the complete
 order-three support-union obstruction, with no algebraic pencil certificate. -/
 theorem first_sector_ne_six (S : Finset Word6) (ξ : Bool)
     (hbound : ∀ p η, (sector S p η).card ≤ 6)
     (hcomplete : ∀ p η, (sector S p η).card = 6 → CompleteSector S p η)
     (hcomp : ∀ x ∈ sector S (Equiv.refl _) ξ, complement x ∈ sector S (Equiv.refl _) ξ)
     (hpar : ∀ x ∈ sector S (Equiv.refl _) ξ, ∀ y ∈ sector S (Equiv.refl _) ξ,
       parity x = parity y) :
     (sector S (Equiv.refl _) ξ).card ≠ 6 := by
   intro hcard
   obtain ⟨a,ha⟩ := six_union_threeBlocks _ hcard hcomp hpar
   have hseed : seed a ξ ⊆ S := seed_subset S a ξ ha (hcomplete _ _ hcard)
   have hpair (η : Bool) : (sector S pair02 η).card = 6 := by
     have hh := Finset.card_le_card (sector_mono hseed pair02 η)
     rw [seed_pair02_card] at hh
     exact Nat.le_antisymm (hbound _ _) hh
   have hfilled : completion (seed a ξ) pair02 ⊆ S :=
     (completion_mono hseed pair02).trans
       (completion_subset S pair02 (fun η => hcomplete _ _ (hpair η)))
   have hh := Finset.card_le_card (sector_mono hfilled pair03 false)
   rw [completion_pair03_card] at hh
   have hb := hbound pair03 false
   omega

end
end Paper2.HeightOne.Dihedral.SixPortSupport
