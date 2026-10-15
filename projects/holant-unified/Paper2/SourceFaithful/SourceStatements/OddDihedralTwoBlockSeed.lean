import Paper2.HeightOne.Dihedral.SixPortPorts

/-! A two-block eight-word seed cannot have any opposite-head-sector
extension under the literal four-word projection bound. Only a small Boolean
incidence lemma is checked finitely; the extension argument applies to every
actual support, without assuming membership in an enumerated support list. -/
namespace Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion
open Paper2.HeightOne Paper2.HeightOne.Dihedral
open SixPortSupport
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def twoBlocks (a b : Word4) : Finset Word4 := by
  classical
  exact {a,complement a,b,complement b}

def twoBlockSeed (a b : Word4) (xi : Bool) : Finset Word6 := by
  classical
  exact Finset.univ.filter (fun x =>
    (x 0 ^^ x 1) = xi ∧ residual x ∈ twoBlocks a b)

theorem balanced_cross_pair : ∀ a b : Word4,
    a ≠ b → b ≠ complement a → parity a = parity b →
    ∃ i j : Fin 4, i ≠ j ∧ ∀ xi eta : Bool,
      (sector (twoBlockSeed a b xi) (pairPerm (tailPort i) (tailPort j)) eta).card = 4 := by
  decide +kernel

theorem residual_lift (p : Equiv.Perm (Fin 6)) (xi b : Bool) (r : Word4) :
    residual ((lift p xi b r) ∘ p) = r := by
  funext i
  simp only [SixPortSupport.residual,Function.comp_apply,lift,Equiv.symm_apply_apply,extend,Fin.cons_succ]

/-- A literal cross-pair card has one supported lift at a residual word and
the opposite supported lift at its complement. The two unwanted lifts violate
the original head parity. -/
theorem two_block_seed_cross_lifts : ∀ a b : Word4, ∀ xi : Bool,
    ∃ eta : Bool, ∃ r : Word4,
      lift pair02 eta false r ∈ twoBlockSeed a b xi ∧
      lift pair02 eta true r ∉ twoBlockSeed a b xi ∧
      lift pair02 eta false (complement r) ∉ twoBlockSeed a b xi := by
  decide +kernel

theorem residual_agrees_outside (p : Equiv.Perm (Fin 6)) (x y : Word6)
    (h : residual (x ∘ p) = residual (y ∘ p)) (k : Fin 6)
    (h0 : k ≠ p 0) (h1 : k ≠ p 1) : x k = y k := by
  obtain ⟨i,hi⟩ := (tailMap_bijective p).surjective ⟨k,h0,h1⟩
  have hh := congrFun h i
  change x (p (tailPort i)) = y (p (tailPort i)) at hh
  have hi' : p (tailPort i) = k := congrArg Subtype.val hi
  rwa [hi'] at hh

theorem two_block_seed_no_opposite (a b : Word4) (xi : Bool)
    (hab : a ≠ b) (hbc : b ≠ complement a) (hpar : parity a = parity b)
    (S : Finset Word6) (hseed : twoBlockSeed a b xi ⊆ S)
    (hbound : ∀ p eta, (sector S p eta).card ≤ 4) :
    ∀ x ∈ S, (x 0 ^^ x 1) = xi := by
  classical
  obtain ⟨i,j,hij,hcard⟩ := balanced_cross_pair a b hab hbc hpar
  let p := pairPerm (tailPort i) (tailPort j)
  have htail : tailPort i ≠ tailPort j := by
    intro h
    exact hij (Fin.succ_injective _ (Fin.succ_injective _ h))
  have hp0 : p 0 = tailPort i := pairPerm_zero _ _ htail
  have hp1 : p 1 = tailPort j := pairPerm_one _ _
  intro x hx
  by_contra hxi
  let eta := x (p 0) ^^ x (p 1)
  let r := residual (x ∘ p)
  have hr : r ∈ sector S p eta := by
    apply (mem_sector S p eta r).mpr
    exact ⟨x (p 0),by simpa only [eta,r,lift_residual] using hx⟩
  have hn : r ∉ sector (twoBlockSeed a b xi) p eta := by
    intro hmem
    obtain ⟨z,hz⟩ := (mem_sector _ p eta r).mp hmem
    let y := lift p eta z r
    have hy : (y 0 ^^ y 1) = xi :=
      (by simpa only [twoBlockSeed,Finset.mem_filter,Finset.mem_univ,true_and,y]
        using hz : (y 0 ^^ y 1) = xi ∧ residual y ∈ twoBlocks a b).1
    have he : residual (x ∘ p) = residual (y ∘ p) :=
      (residual_lift p eta z r).symm
    have h00 : (0 : Fin 6) ≠ p 0 := by rw [hp0]; exact (tailPort_ne_zero i).symm
    have h01 : (0 : Fin 6) ≠ p 1 := by rw [hp1]; exact (tailPort_ne_zero j).symm
    have h10 : (1 : Fin 6) ≠ p 0 := by rw [hp0]; exact (tailPort_ne_one i).symm
    have h11 : (1 : Fin 6) ≠ p 1 := by rw [hp1]; exact (tailPort_ne_one j).symm
    have hx0 := residual_agrees_outside p x y he 0 h00 h01
    have hx1 := residual_agrees_outside p x y he 1 h10 h11
    exact hxi (by rwa [hx0,hx1])
  have hsub : insert r (sector (twoBlockSeed a b xi) p eta) ⊆ sector S p eta := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hr
    · exact sector_mono hseed p eta hw
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hn,hcard xi eta] at hle
  have hbnd := hbound p eta
  omega

end
end Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion

