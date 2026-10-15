import Paper2.HeightOne.Dihedral.SixPortAllCards

/-! Coefficient identities for Appendix A.1(ii).  These statements include
two-word generalized-equality cards.  No four-word matching support is used. -/
namespace Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion

open Paper2.HeightOne.Dihedral
open Paper2.HeightOne.Dihedral.SixPortSupport
open Paper2.HeightOne.Dihedral.SixPortPencils
open Paper2.Tractable Paper2.HeightOne Paper2.HeightOne.Cyclic
set_option maxRecDepth 2048

variable {K : Type} [Field K]

omit [Field K] in
theorem first_ordered_reindex (f : Signature K 6) (p q : Equiv.Perm (Fin 6)) (xi : Bool) :
    first (Tensor.reindex p.symm f) q xi = first f (q.trans p) xi := rfl

omit [Field K] in
theorem second_ordered_reindex (f : Signature K 6) (p q : Equiv.Perm (Fin 6)) (xi : Bool) :
    second (Tensor.reindex p.symm f) q xi = second f (q.trans p) xi := rfl

/-- A zero at one cube-root phase and complement-cube equality at a second
phase identify the cubed coefficients of the two source slices. -/
theorem cancelled_phase_source_cube (a b c d s t : K)
    (hs : s ^ 3 = 1) (hst : s ≠ t)
    (hzero : a - s * b = 0)
    (hscube : (c - s * d) ^ 3 = (a - s * b) ^ 3)
    (htcube : (c - t * d) ^ 3 = (a - t * b) ^ 3) :
    c ^ 3 = b ^ 3 ∧ d ^ 3 = a ^ 3 := by
  have ha : a = s * b := sub_eq_zero.mp hzero
  have hc : c = s * d := by
    apply sub_eq_zero.mp
    have h := hscube
    rw [hzero, zero_pow (by decide : 3 ≠ 0)] at h
    by_contra hn
    exact (pow_ne_zero 3 hn) h
  have hdiff : s - t ≠ 0 := sub_ne_zero.mpr hst
  have hd : d ^ 3 = b ^ 3 := by
    have h := htcube
    rw [ha, hc, ← sub_mul, ← sub_mul, mul_pow, mul_pow] at h
    exact mul_left_cancel₀ (pow_ne_zero 3 hdiff) h
  constructor
  · rw [hc, mul_pow, hs, one_mul, hd]
  · rw [ha, mul_pow, hs, one_mul, hd]

/-- For disjoint surviving phase supports, each joint coordinate has two
nonzero source entries.  This is valid for two-word cards. -/
theorem disjoint_pencils_source_nonzero {X : Type*} [Fintype X]
    (A B : X → K) (s t : K) (hs : s ≠ 0) (ht : t ≠ 0)
    (hdisjoint : Disjoint (pencilSupport A B s) (pencilSupport A B t))
    (x : X) (hx : x ∈ jointSupport A B) : A x ≠ 0 ∧ B x ≠ 0 := by
  classical
  have hz : A x - s * B x = 0 ∨ A x - t * B x = 0 := by
    by_contra h
    push Not at h
    exact (Finset.disjoint_left.mp hdisjoint)
      ((mem_pencilSupport A B s x).mpr h.1)
      ((mem_pencilSupport A B t x).mpr h.2)
  have hb : B x ≠ 0 := by
    intro hb
    have ha : A x = 0 := by
      rcases hz with h | h <;> simpa [hb] using h
    exact (mem_jointSupport A B x).mp hx |>.elim (fun h => h ha) (fun h => h hb)
  refine ⟨?_, hb⟩
  intro ha
  rcases hz with h | h
  · exact (mul_ne_zero hs hb) (by simpa [ha] using (sub_eq_zero.mp h).symm)
  · exact (mul_ne_zero ht hb) (by simpa [ha] using (sub_eq_zero.mp h).symm)

/-- Disjoint cube-root phase supports force the source complement pairs to
have equal cubes, with the two slices exchanged. -/
theorem disjoint_pencils_source_cube {X : Type*} [Fintype X]
    (A B : X → K) (comp : X → X) (s t : K)
    (hs : s ^ 3 = 1) (ht : t ^ 3 = 1) (hst : s ≠ t)
    (hdisjoint : Disjoint (pencilSupport A B s) (pencilSupport A B t))
    (hscube : ∀ x, (A (comp x) - s * B (comp x)) ^ 3 = (A x - s * B x) ^ 3)
    (htcube : ∀ x, (A (comp x) - t * B (comp x)) ^ 3 = (A x - t * B x) ^ 3)
    (x : X) : A (comp x) ^ 3 = B x ^ 3 ∧ B (comp x) ^ 3 = A x ^ 3 := by
  classical
  by_cases hzero : A x - s * B x = 0
  · exact cancelled_phase_source_cube _ _ _ _ _ _ hs hst hzero (hscube x) (htcube x)
  · have hz : A x - t * B x = 0 := by
      by_contra htzero
      exact (Finset.disjoint_left.mp hdisjoint)
        ((mem_pencilSupport A B s x).mpr hzero)
        ((mem_pencilSupport A B t x).mpr htzero)
    exact cancelled_phase_source_cube _ _ _ _ _ _ ht hst.symm hz (htcube x) (hscube x)

/-- Cross-pair contraction of a matching cube produces a minus sign between
complement cubes.  It cannot satisfy the atlas identity when the source cube
is nonzero. -/
theorem cross_card_cube_contradiction [CharZero K] (a b s : K)
    (ha : a ≠ 0) (hs : s ^ 3 = 1) (hab : b ^ 3 = a ^ 3)
    (hcard : (-s * b) ^ 3 = a ^ 3) : False := by
  have hneg : -(a ^ 3) = a ^ 3 := by
    calc
      -(a ^ 3) = -((s ^ 3) * b ^ 3) := by rw [hs, hab, one_mul]
      _ = (-s * b) ^ 3 := by ring
      _ = a ^ 3 := hcard
  have htwo : (2 : K) * a ^ 3 = 0 := by linear_combination -hneg
  exact (mul_ne_zero (by norm_num : (2 : K) ≠ 0) (pow_ne_zero 3 ha)) htwo

/-- The generic-field ordered-sector bound. The coefficient counting and
Boolean incidence argument do not use algebraicity. -/
theorem ordered_union_card_le_four (f : Signature K 6) (hpar : HasParity f)
    (S : Finset K) (hS : S.card = 3) (hsne : ∀ s ∈ S, s ≠ 0)
    (hcards : ∀ p xi s, s ∈ S → (pencilSupport (first f p xi) (second f p xi) s).card ≤ 4)
    (hcomp : ∀ p xi s, s ∈ S → ∀ x ∈ pencilSupport (first f p xi) (second f p xi) s,
      complement x ∈ pencilSupport (first f p xi) (second f p xi) s)
    (p : Equiv.Perm (Fin 6)) (xi : Bool) :
    (jointSupport (first f p xi) (second f p xi)).card ≤ 4 := by
  have hh := three_phase_union_card_le_four (Tensor.reindex p.symm f)
    (hasParity_reindex p.symm f hpar) S hS hsne
    (fun q eta s hs => by simpa only [first_ordered_reindex,second_ordered_reindex] using hcards (q.trans p) eta s hs)
    (fun q eta s hs => by simpa only [first_ordered_reindex,second_ordered_reindex] using hcomp (q.trans p) eta s hs) xi
  simpa only [first_ordered_reindex,second_ordered_reindex,Equiv.refl_trans] using hh

/-- The three-block line has six joint support words.  The global pencil
bound excludes it even when some contractions have only two live words. -/
theorem three_block_union_excluded (f : Signature K 6)
    (hpar : HasParity f) (S : Finset K)
    (hS : S.card = 3) (hsne : ∀ s ∈ S, s ≠ 0)
    (hcards : ∀ p ξ s, s ∈ S →
      (pencilSupport (first f p ξ) (second f p ξ) s).card ≤ 4)
    (hcomp : ∀ p ξ s, s ∈ S →
      ∀ x ∈ pencilSupport (first f p ξ) (second f p ξ) s,
        complement x ∈ pencilSupport (first f p ξ) (second f p ξ) s)
    (p : Equiv.Perm (Fin 6)) (ξ : Bool)
    (hsix : (jointSupport (first f p ξ) (second f p ξ)).card = 6) : False := by
  have h := ordered_union_card_le_four f hpar S hS hsne hcards hcomp p ξ
  omega

end Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion
