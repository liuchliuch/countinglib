import Paper2.HeightOne.GroupSplit.GroupReduction
import Paper2.HeightOne.GroupSplit.OddGenerator
import Paper2.HeightOne.GroupSplit.RotationShape

/-! The surviving odd group admits one legal algebraic diagonal normalization,
with equality of the complete group and actual representatives of every class. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.GroupSplit
open MatrixGroup Tractable FiniteGroupFacts.ProjectiveCentralizers
noncomputable section

def cyclicPhaseClasses (N : ℕ) : Set (PGL2 AlgebraicComplex) :=
  phaseHom '' (rootsOfUnity N AlgebraicComplex : Set AlgebraicComplexˣ)

def dihedralPhaseClasses (N : ℕ) : Set (PGL2 AlgebraicComplex) :=
  cyclicPhaseClasses N ∪ (fun q => zClass * q) '' cyclicPhaseClasses N

lemma diagonal_fixes_z (D : InvertibleKernel) (q : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel q 1) :
    pglMk _ (basisGL D) * zClass * (pglMk _ (basisGL D))⁻¹ = zClass := by
  have hc : Commute (pglMk _ (basisGL D)) zClass := by
    change pglMk _ (basisGL D) * pglMk _ zGL = pglMk _ zGL * pglMk _ (basisGL D)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Units.ext
    change Matrix.of D.matrix * (zGL : AMat) = (zGL : AMat) * Matrix.of D.matrix
    rw [hD]
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.mul_apply, zGL, diagonalGL, diagonal, diagonalKernel]
  rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]

lemma rotation_matrix_shape (R : Matrix.GeneralLinearGroup Bool AlgebraicComplex)
    (N : ℕ) (hN : 3 ≤ N) (ho : orderOf (pglMk _ R) = N)
    (hrel : zClass * pglMk _ R * zClass = (pglMk _ R)⁻¹) :
    ∃ a b c : AlgebraicComplex, b ≠ 0 ∧ c ≠ 0 ∧ (R : AMat) = balanced a b c := by
  have hfin : ProjectivelyFinite (R : AMat) := (isOfFinOrder_pglMk_iff R).mp
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨N, by omega, by rw [← ho]; exact pow_orderOf_eq_one _⟩)
  apply rotation_balanced_shape R (Matrix.GeneralLinearGroup.det_ne_zero R) hfin
  · rintro ⟨c, hc, he⟩
    have hp : (pglMk _ R) ^ 2 = 1 := by
      rw [← map_pow]
      change pglMk _ (R ^ 2) = pglMk _ 1
      exact pglMk_eq_iff_projectiveClass_eq.mpr (projectiveClass_eq_iff.mpr ⟨c, hc, he⟩)
    have hd : N ∣ 2 := ho ▸ orderOf_dvd_of_pow_eq_one hp
    have := Nat.le_of_dvd (by omega : 0 < 2) hd
    omega
  · have hp : pglMk _ (zGL * R * zGL * R) = pglMk _ 1 := by
      simp only [map_mul, map_one]
      change zClass * pglMk _ R * zClass * pglMk _ R = 1
      rw [hrel, inv_mul_cancel]
    obtain ⟨c, hc, he⟩ := projectiveClass_eq_iff.mp (pglMk_eq_iff_projectiveClass_eq.mp hp)
    exact ⟨c, hc, he⟩

/-- The full normalization theorem for a surviving odd rotation, independently
of any chosen finite enumeration of the directly realizable binaries. -/
theorem normalize_complete_odd_group (F : SignatureFamily AlgebraicComplex)
    (hG : ProjectiveMatrixGroup (actualTransfers F))
    (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N) (r : PGL2 AlgebraicComplex)
    (hrot : RotationData (projectiveSubgroup hG) zClass N r) :
    ∃ (q : AlgebraicComplex) (D : InvertibleKernel),
      q ≠ 0 ∧ D.matrix = diagonalKernel q 1 ∧ XConformal D ∧
      (actualClasses (familyAction D F) = cyclicPhaseClasses N ∨
       actualClasses (familyAction D F) = dihedralPhaseClasses N) := by
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨R, hR, hRclass⟩ := hrot.1
  have horder : orderOf (pglMk _ R) = N := hRclass ▸ hrot.2.1
  have hrel : zClass * pglMk _ R * zClass = (pglMk _ R)⁻¹ := hRclass ▸ hrot.2.2.1
  obtain ⟨a, b, c, hb, hc, hRmat⟩ := rotation_matrix_shape R N hN horder hrel
  obtain ⟨q, D, s, hq, hD, hconf, hnorm, hsorder⟩ :=
    balanced_projective_normalization R a b c hRmat hb hc
  have hsN : orderOf s = N := hsorder.trans horder
  let C : MulAut (PGL2 AlgebraicComplex) := MulAut.conj (pglMk _ (basisGL D))
  have hCr : C r = phaseHom s := by
    simpa only [C, MulAut.conj_apply, hRclass] using hnorm
  have hCz : C zClass = zClass := diagonal_fixes_z D q hD
  have htrans : actualClasses (familyAction D F) =
      ((projectiveSubgroup hG).map C.toMonoidHom : Set (PGL2 AlgebraicComplex)) := by
    rw [completeClasses_diagonal_transport F D q 1 hD hq one_ne_zero]
    rfl
  have hnew := hrot.map C.toMonoidHom C.injective
  have hset := hnew.2.2.2
  change ((projectiveSubgroup hG).map C.toMonoidHom : Set (PGL2 AlgebraicComplex)) =
      (Subgroup.zpowers (C r) : Set (PGL2 AlgebraicComplex)) ∨
    ((projectiveSubgroup hG).map C.toMonoidHom : Set (PGL2 AlgebraicComplex)) =
      (Subgroup.zpowers (C r) : Set (PGL2 AlgebraicComplex)) ∪
        (fun x => C zClass * x) '' (Subgroup.zpowers (C r) : Set (PGL2 AlgebraicComplex)) at hset
  rw [hCr, hCz, phase_zpowers_eq_roots s hsN] at hset
  exact ⟨q, D, hq, hD, hconf, by simpa only [htrans, cyclicPhaseClasses, dihedralPhaseClasses] using hset⟩

/-- Complete-set membership retains a literal nonsingular ordered-binary graph
witness; its transfer differs only by one recorded nonzero scalar. -/
lemma actualClass_representative {F : SignatureFamily AlgebraicComplex}
    {q : PGL2 AlgebraicComplex} (hq : q ∈ actualClasses F) :
    ∃ B : AMat, ActualNonsingular F B ∧
      projectiveClass (transfer B) = pglToProjectiveClass q := by
  obtain ⟨U, ⟨B, hB, c, hc, hU⟩, rfl⟩ := hq
  refine ⟨B, hB, ?_⟩
  rw [pglToProjectiveClass_mk, hU, projectiveClass_smul _ hc]


lemma z_not_cyclicPhaseClasses (N : ℕ) : zClass ∉ cyclicPhaseClasses N := by
  rintro ⟨s, hs, he⟩
  obtain ⟨c, hc, hm⟩ := projectiveClass_eq_iff.mp (pglMk_eq_iff_projectiveClass_eq.mp he)
  have h0 := congrArg (fun M : AMat => M false false + M false true) hm
  have h1 := congrArg (fun M : AMat => M true false + M true true) hm
  have hrow : phase (s : AlgebraicComplex) true false + phase (s : AlgebraicComplex) true true = 1 := by
    dsimp [phase, balanced]
    field_simp
    ring
  change phase (s : AlgebraicComplex) false false + phase (s : AlgebraicComplex) false true = _ at h0
  change phase (s : AlgebraicComplex) true false + phase (s : AlgebraicComplex) true true = _ at h1
  rw [phase_row_sum] at h0
  rw [hrow] at h1
  simp [zGL, diagonalGL, diagonal, Matrix.smul_apply] at h0 h1
  have hbad : (2 : AlgebraicComplex) = 0 := by linear_combination h0 + h1
  norm_num at hbad

lemma z_mem_dihedralPhaseClasses (N : ℕ) : zClass ∈ dihedralPhaseClasses N := by
  right
  refine ⟨1, ?_, by simp⟩
  refine ⟨1, (rootsOfUnity N AlgebraicComplex).one_mem, map_one phaseHom⟩

lemma cyclicPhaseClasses_ne_dihedralPhaseClasses (N : ℕ) :
    cyclicPhaseClasses N ≠ dihedralPhaseClasses N := by
  intro he
  exact z_not_cyclicPhaseClasses N (he ▸ z_mem_dihedralPhaseClasses N)

lemma normalized_forms_exclusive {S : Set (PGL2 AlgebraicComplex)} {N : ℕ}
    (h : S = cyclicPhaseClasses N ∨ S = dihedralPhaseClasses N) :
    Xor (S = cyclicPhaseClasses N) (S = dihedralPhaseClasses N) := by
  rw [xor_iff_or_and_not_and]
  refine ⟨h, ?_⟩
  rintro ⟨hc, hd⟩
  exact cyclicPhaseClasses_ne_dihedralPhaseClasses N (hc.symm.trans hd)

/-- A simultaneous fixed choice of actual representatives, with all nonzero
scalars retained by the projective transfer equality. -/
theorem fixed_actualClass_representatives (F : SignatureFamily AlgebraicComplex) :
    ∃ rep : actualClasses F → AMat, ∀ u : actualClasses F,
      ActualNonsingular F (rep u) ∧
        projectiveClass (transfer (rep u)) = pglToProjectiveClass u := by
  choose rep hrep using (fun u : actualClasses F => actualClass_representative u.property)
  exact ⟨rep, hrep⟩

end
end Paper2.HeightOne.GroupSplit
