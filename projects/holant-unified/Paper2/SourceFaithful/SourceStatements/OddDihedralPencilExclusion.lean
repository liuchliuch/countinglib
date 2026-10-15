import Paper2.SourceFaithful.SourceStatements.OddDihedralPencilSupport

/-! The switching exclusions of Appendix A.1(ii), proved symbolically over
every field of characteristic zero.  The hypotheses are weaker than membership in
the 66-point atlas: only the actual four-word bound and complement-cube
identity are used. In particular, two-word generalized-equality points are
retained. -/
namespace Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion
open Paper2.Tractable Paper2.HeightOne Paper2.HeightOne.Dihedral
open SixPortSupport SixPortPencils
noncomputable section
set_option maxRecDepth 4096
local instance {α : Type*} : DecidableEq α := Classical.decEq α

variable {K : Type} [Field K]

theorem cube_root_nonzero (s : K) (hs : s ^ 3 = 1) : s ≠ 0 := by
  intro hz
  simp [hz] at hs

theorem complement_support_of_cube (A B : Word4 → K) (s : K)
    (hcube : ∀ r, (A (complement r) - s * B (complement r)) ^ 3 =
      (A r - s * B r) ^ 3) :
    ∀ r ∈ pencilSupport A B s, complement r ∈ pencilSupport A B s := by
  intro r hr
  rw [mem_pencilSupport] at hr ⊢
  intro hz
  have h := hcube r
  rw [hz,zero_pow (by decide : 3 ≠ 0)] at h
  exact (pow_ne_zero 3 hr) h.symm

theorem selected_source_complement_cube (f : Signature K 6) (xi : Bool)
    (s t : K) (hs : s ^ 3 = 1) (ht : t ^ 3 = 1) (hst : s ≠ t)
    (hdis : Disjoint
      (pencilSupport (first f (Equiv.refl _) xi) (second f (Equiv.refl _) xi) s)
      (pencilSupport (first f (Equiv.refl _) xi) (second f (Equiv.refl _) xi) t))
    (hscube : ∀ r,
      (first f (Equiv.refl _) xi (complement r) - s * second f (Equiv.refl _) xi (complement r)) ^ 3 =
      (first f (Equiv.refl _) xi r - s * second f (Equiv.refl _) xi r) ^ 3)
    (htcube : ∀ r,
      (first f (Equiv.refl _) xi (complement r) - t * second f (Equiv.refl _) xi (complement r)) ^ 3 =
      (first f (Equiv.refl _) xi r - t * second f (Equiv.refl _) xi r) ^ 3)
    (x : Word6) (hx : (x 0 ^^ x 1) = xi) :
    f (sixComplement x) ^ 3 = f x ^ 3 := by
  have hc := disjoint_pencils_source_cube _ _ complement s t hs ht hst hdis hscube htcube
  have he : lift (Equiv.refl _) xi (x 0) (residual x) = x := by
    rw [← hx]
    simpa using lift_residual (Equiv.refl (Fin 6)) x
  rw [← he, sixComplement_lift]
  cases hb : x 0
  · simpa [first,second,hb] using (hc (residual x)).2
  · simpa [first,second,hb] using (hc (residual x)).1

theorem secant_excluded_canonical [CharZero K] (f : Signature K 6) (hpar : HasParity f)
    (S : Finset K) (hS : S.card = 3)
    (hroot : ∀ s ∈ S, s ^ 3 = 1)
    (hcards : ∀ p xi s, s ∈ S →
      (pencilSupport (first f p xi) (second f p xi) s).card ≤ 4)
    (hcube : ∀ p xi s, s ∈ S → ∀ r,
      (first f p xi (complement r) - s * second f p xi (complement r)) ^ 3 =
      (first f p xi r - s * second f p xi r) ^ 3)
    (xi : Bool) (s t : K) (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t)
    (hscard : (pencilSupport (first f (Equiv.refl _) xi) (second f (Equiv.refl _) xi) s).card = 2)
    (htcard : (pencilSupport (first f (Equiv.refl _) xi) (second f (Equiv.refl _) xi) t).card = 2)
    (hdis : Disjoint
      (pencilSupport (first f (Equiv.refl _) xi) (second f (Equiv.refl _) xi) s)
      (pencilSupport (first f (Equiv.refl _) xi) (second f (Equiv.refl _) xi) t)) : False := by
  have hsne : ∀ q ∈ S, q ≠ 0 := fun q hq => cube_root_nonzero q (hroot q hq)
  have hcomp : ∀ p eta q, q ∈ S →
      ∀ r ∈ pencilSupport (first f p eta) (second f p eta) q,
        complement r ∈ pencilSupport (first f p eta) (second f p eta) q := by
    intro p eta q hq
    exact complement_support_of_cube _ _ q (hcube p eta q hq)
  have hbound : ∀ p eta, (sector (support f) p eta).card ≤ 4 := by
    intro p eta
    rw [← joint_sector]
    exact ordered_union_card_le_four f hpar S hS hsne hcards hcomp p eta
  obtain ⟨a,b,hab,hbc,hp,hseed⟩ := secant_support_is_seed f hpar xi s t hst
    (hsne s hs) (hsne t ht) hscard htcard hdis (hcomp _ _ s hs) (hcomp _ _ t ht) hbound
  obtain ⟨eta,r,hr,hrtrue,hrcomp⟩ := two_block_seed_cross_lifts a b xi
  have hn : f (lift pair02 eta false r) ≠ 0 := by
    have hm : lift pair02 eta false r ∈ support f := by rwa [hseed]
    simpa [support] using hm
  have hz : f (lift pair02 eta true r) = 0 := by
    by_contra h
    exact hrtrue (by rw [← hseed]; simpa [support] using h)
  have hzc : f (lift pair02 eta false (complement r)) = 0 := by
    by_contra h
    exact hrcomp (by rw [← hseed]; simpa [support] using h)
  have hhead : ((lift pair02 eta false r) 0 ^^ (lift pair02 eta false r) 1) = xi :=
    (by simpa [twoBlockSeed] using hr :
      _ = xi ∧ residual (lift pair02 eta false r) ∈ twoBlocks a b).1
  have hsource := selected_source_complement_cube f xi s t (hroot s hs) (hroot t ht)
    hst hdis (hcube _ xi s hs) (hcube _ xi t ht) (lift pair02 eta false r) hhead
  rw [sixComplement_lift] at hsource
  have hcc := hcube pair02 eta s hs r
  change (f (lift pair02 eta false (complement r)) - s * f (lift pair02 eta true (complement r))) ^ 3 =
    (f (lift pair02 eta false r) - s * f (lift pair02 eta true r)) ^ 3 at hcc
  rw [hzc,hz,zero_sub,mul_zero,sub_zero] at hcc
  apply cross_card_cube_contradiction _ _ s hn (hroot s hs) hsource
  simpa only [Bool.not_false,neg_mul] using hcc

/-- Arbitrary ordered-port switching excludes the secant (1/1/2) line.
The original six-port signature may have arbitrary coefficients. -/
theorem secant_excluded [CharZero K] (f : Signature K 6) (hpar : HasParity f)
    (S : Finset K) (hS : S.card = 3)
    (hroot : ∀ s ∈ S, s ^ 3 = 1)
    (hcards : ∀ p xi s, s ∈ S →
      (pencilSupport (first f p xi) (second f p xi) s).card ≤ 4)
    (hcube : ∀ p xi s, s ∈ S → ∀ r,
      (first f p xi (complement r) - s * second f p xi (complement r)) ^ 3 =
      (first f p xi r - s * second f p xi r) ^ 3)
    (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (s t : K) (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t)
    (hscard : (pencilSupport (first f p xi) (second f p xi) s).card = 2)
    (htcard : (pencilSupport (first f p xi) (second f p xi) t).card = 2)
    (hdis : Disjoint (pencilSupport (first f p xi) (second f p xi) s)
      (pencilSupport (first f p xi) (second f p xi) t)) : False := by
  apply secant_excluded_canonical (Tensor.reindex p.symm f)
    (hasParity_reindex p.symm f hpar) S hS hroot
    (fun q eta v hv => by simpa only [first_ordered_reindex,second_ordered_reindex] using hcards (q.trans p) eta v hv)
    (fun q eta v hv r => by simpa only [first_ordered_reindex,second_ordered_reindex] using hcube (q.trans p) eta v hv r)
    xi s t hs ht hst
  · simpa only [first_ordered_reindex,second_ordered_reindex,Equiv.refl_trans] using hscard
  · simpa only [first_ordered_reindex,second_ordered_reindex,Equiv.refl_trans] using htcard
  · simpa only [first_ordered_reindex,second_ordered_reindex,Equiv.refl_trans] using hdis

/-- The three-block (2/2/2) line is excluded by the same literal card
invariants, including all zero or two-word cards. -/
theorem three_block_excluded (f : Signature K 6) (hpar : HasParity f)
    (S : Finset K) (hS : S.card = 3)
    (hroot : ∀ s ∈ S, s ^ 3 = 1)
    (hcards : ∀ p xi s, s ∈ S →
      (pencilSupport (first f p xi) (second f p xi) s).card ≤ 4)
    (hcube : ∀ p xi s, s ∈ S → ∀ r,
      (first f p xi (complement r) - s * second f p xi (complement r)) ^ 3 =
      (first f p xi r - s * second f p xi r) ^ 3)
    (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (hsix : (jointSupport (first f p xi) (second f p xi)).card = 6) : False := by
  exact three_block_union_excluded f hpar S hS
    (fun s hs => cube_root_nonzero s (hroot s hs)) hcards
    (fun q eta s hs => complement_support_of_cube _ _ s (hcube q eta s hs)) p xi hsix

end
end Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion

