import Paper2.HeightOne.GroupSplit.PGL
import Paper2.HeightTwo.Normalization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Exact source normalization in the algebraic-complex field. The only matrix
applied to signatures is the legal diagonal GO(X) basis. -/
namespace Paper2.HeightOne.GroupSplit
open Tractable
noncomputable section

abbrev AMat := Matrix Bool Bool AlgebraicComplex

/-- The rotation representative after the dihedral relation has forced equal diagonals. -/
def balanced (a b c : AlgebraicComplex) : AMat :=
  fun i j => if i then (if j then a else c) else (if j then b else a)

/-- The literal phase matrix from Theorem 5.4. -/
def phase (s : AlgebraicComplex) : AMat :=
  balanced ((1 + s) / 2) ((1 - s) / 2) ((1 - s) / 2)

lemma phase_mul (s t : AlgebraicComplex) : phase s * phase t = phase (s * t) := by
  ext i j
  cases i <;> cases j <;> simp only [phase, balanced, Matrix.mul_apply, Fintype.sum_bool, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] <;> field_simp <;> ring

@[simp] lemma phase_one : phase 1 = 1 := by
  ext i j
  cases i <;> cases j <;> simp [phase, balanced]

lemma phase_row_sum (s : AlgebraicComplex) :
    phase s false false + phase s false true = 1 := by
  dsimp [phase, balanced]
  field_simp
  ring

lemma phase_scalar_injective {s t c : AlgebraicComplex}
    (h : phase s = c • phase t) : s = t := by
  have h0 := congrArg (fun M : AMat => M false false + M false true) h
  simp only [Matrix.smul_apply, smul_eq_mul, ← mul_add, phase_row_sum, mul_one] at h0
  have h00 := congrArg (fun M : AMat => M false false) h
  simp only [Matrix.smul_apply, smul_eq_mul, ← h0, one_mul, phase, balanced,
    Bool.false_eq_true, ↓reduceIte] at h00
  exact (div_left_inj' (by norm_num : (2 : AlgebraicComplex) ≠ 0)).mp h00 |> add_left_cancel

/-- Genuine invertible phase matrix; the inverse is recorded literally. -/
def phaseGL (s : AlgebraicComplexˣ) : Matrix.GeneralLinearGroup Bool AlgebraicComplex where
  val := phase s
  inv := phase ↑s⁻¹
  val_inv := by rw [phase_mul]; simp
  inv_val := by rw [phase_mul]; simp

def phaseHom : AlgebraicComplexˣ →* PGL2 AlgebraicComplex where
  toFun s := pglMk _ (phaseGL s)
  map_one' := by
    change pglMk _ (phaseGL 1) = 1
    have h : phaseGL 1 = 1 := Units.ext phase_one
    rw [h, map_one]
  map_mul' s t := by
    rw [← map_mul]
    congr 1
    exact Units.ext (phase_mul s t).symm

lemma phaseHom_injective : Function.Injective phaseHom := by
  intro s t h
  obtain ⟨c, hc, he⟩ := projectiveClass_eq_iff.mp
    (pglMk_eq_iff_projectiveClass_eq.mp h)
  exact Units.ext (phase_scalar_injective he)

lemma phaseHom_order (s : AlgebraicComplexˣ) :
    orderOf (phaseHom s) = orderOf s :=
  orderOf_injective phaseHom phaseHom_injective s

lemma exists_ratio_square_root (b c : AlgebraicComplex) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ q : AlgebraicComplex, q ≠ 0 ∧ q ^ 2 = c / b := by
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨q, hq⟩ := IsAlgClosed.exists_pow_nat_eq (c / b) (by decide : 0 < 2)
  refine ⟨q, ?_, hq⟩
  intro hzero
  have hz : c / b = 0 := by rw [← hq, hzero]; simp
  exact (div_ne_zero hc hb) hz

lemma ratio_square_root_cross {b c q : AlgebraicComplex}
    (hb : b ≠ 0) (hq : q ^ 2 = c / b) : q * (q * b) = c := by
  rw [← mul_assoc, ← pow_two, hq, div_mul_cancel₀ _ hb]

lemma diagonal_conjugates_balanced (a b c q : AlgebraicComplex)
    (hq0 : q ≠ 0) (hq : q ^ 2 = c / b) (hb : b ≠ 0) :
    Kernel.mul (Kernel.mul (HeightTwo.diagonalBasis q 1 hq0 one_ne_zero).matrix
      (balanced a b c)) (HeightTwo.diagonalBasis q 1 hq0 one_ne_zero).inverse =
        balanced a (q * b) (q * b) := by
  have hcross := ratio_square_root_cross hb hq
  have he : c * q⁻¹ = q * b := by rw [← hcross]; field_simp
  funext i j
  cases i <;> cases j <;>
    simp [HeightTwo.diagonalBasis, Kernel.mul, diagonalKernel, balanced, hq0, he, mul_assoc, mul_comm]

lemma balanced_det (a b c : AlgebraicComplex) :
    Matrix.det (balanced a b c) = a ^ 2 - b * c := by
  rw [← Matrix.det_reindex_self (e := finTwoEquiv.symm)]
  rw [Matrix.det_fin_two]
  simp [Matrix.reindex, Matrix.submatrix, balanced, finTwoEquiv, pow_two]


/-- The exact legal normalization, including its algebraic root, edge multiplier,
nonzero eigenvalues, and scalar. There is no arbitrary classification conjugator. -/
theorem balanced_algebraic_normalization (a b c : AlgebraicComplex)
    (hb : b ≠ 0) (hc : c ≠ 0) (hdet : a ^ 2 - b * c ≠ 0) :
    ∃ (q δ s lam : AlgebraicComplex) (D : InvertibleKernel),
      q ≠ 0 ∧ q ^ 2 = c / b ∧ δ = q * b ∧
      D.matrix = diagonalKernel q 1 ∧ XConformal D ∧
      Kernel.pullback Signature.disequality D.matrix =
        (fun i j => q * Signature.disequality i j) ∧
      lam = a + δ ∧ lam ≠ 0 ∧ s ≠ 0 ∧ s = (a - δ) / (a + δ) ∧
      Kernel.mul (Kernel.mul D.matrix (balanced a b c)) D.inverse = lam • phase s := by
  obtain ⟨q, hq0, hq⟩ := exists_ratio_square_root b c hb hc
  let δ := q * b
  have hδsq : δ ^ 2 = b * c := by
    dsimp [δ]
    rw [mul_pow, hq]
    field_simp
  have heig : (a + δ) * (a - δ) = a ^ 2 - b * c := by
    rw [← hδsq]
    ring
  have hplus : a + δ ≠ 0 := by
    intro hz
    exact hdet (by rw [← heig, hz, zero_mul])
  have hminus : a - δ ≠ 0 := by
    intro hz
    exact hdet (by rw [← heig, hz, mul_zero])
  refine ⟨q, δ, (a - δ) / (a + δ), a + δ,
    HeightTwo.diagonalBasis q 1 hq0 one_ne_zero,
    hq0, hq, rfl, rfl,
    HeightTwo.diagonalBasis_conformal q 1 hq0 one_ne_zero, ?_, rfl,
    hplus, div_ne_zero hminus hplus, rfl, ?_⟩
  · simpa using HeightTwo.diagonalBasis_pullback q 1 hq0 one_ne_zero
  · rw [diagonal_conjugates_balanced a b c q hq0 hq hb]
    change balanced a δ δ = (a + δ) • phase ((a - δ) / (a + δ))
    ext i j
    cases i <;> cases j <;>
      simp only [phase, balanced, Matrix.smul_apply, smul_eq_mul, Bool.false_eq_true,
        ↓reduceIte] <;> field_simp <;> ring

/-- The displayed phase family is precisely the cyclic subgroup when a primitive
root is supplied. This is equality with all N-th roots, not a selected finite list. -/
theorem phase_zpowers_eq_roots {N : ℕ} [NeZero N] (s : AlgebraicComplexˣ)
    (hs : orderOf s = N) :
    (Subgroup.zpowers (phaseHom s) : Set (PGL2 AlgebraicComplex)) =
      phaseHom '' (rootsOfUnity N AlgebraicComplex : Set AlgebraicComplexˣ) := by
  have hprim : IsPrimitiveRoot s N := IsPrimitiveRoot.iff_orderOf.mpr hs
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨s ^ k, (rootsOfUnity N AlgebraicComplex).zpow_mem hprim.mem_rootsOfUnity k, ?_⟩
    exact map_zpow phaseHom s k
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hprim.eq_pow_of_mem_rootsOfUnity ht
    rw [map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k

/-- Adapter from the project's actual algebraic kernel with two-sided inverse. -/
def basisGL (D : InvertibleKernel) : Matrix.GeneralLinearGroup Bool AlgebraicComplex where
  val := D.matrix
  inv := D.inverse
  val_inv := by
    change Kernel.mul D.matrix D.inverse = _
    rw [D.matrix_inverse]
    ext i j
    cases i <;> cases j <;> simp [Signature.equality]
  inv_val := by
    change Kernel.mul D.inverse D.matrix = _
    rw [D.inverse_matrix]
    ext i j
    cases i <;> cases j <;> simp [Signature.equality]

/-- The normalized primitive phase has exactly the source rotation's projective
order. Conjugacy and scalar removal take place in the genuine PGL quotient. -/
theorem balanced_projective_normalization
    (R : Matrix.GeneralLinearGroup Bool AlgebraicComplex)
    (a b c : AlgebraicComplex) (hR : (R : AMat) = balanced a b c)
    (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ (q : AlgebraicComplex) (D : InvertibleKernel) (s : AlgebraicComplexˣ),
      q ≠ 0 ∧ D.matrix = diagonalKernel q 1 ∧ XConformal D ∧
      pglMk _ (basisGL D) * pglMk _ R * (pglMk _ (basisGL D))⁻¹ = phaseHom s ∧
      orderOf s = orderOf (pglMk _ R) := by
  have hdet : a ^ 2 - b * c ≠ 0 := by
    rw [← balanced_det, ← hR]
    exact Matrix.GeneralLinearGroup.det_ne_zero R
  obtain ⟨q, δ, s, lam, D, hq, hqsq, hδ, hD, hconf, hpull, hlam,
    hlam0, hs0, hs, hnorm⟩ := balanced_algebraic_normalization a b c hb hc hdet
  let su : AlgebraicComplexˣ := Units.mk0 s hs0
  have heq : pglMk _ (basisGL D) * pglMk _ R * (pglMk _ (basisGL D))⁻¹ =
      phaseHom su := by
    rw [← map_inv, ← map_mul, ← map_mul]
    apply pglMk_eq_iff_projectiveClass_eq.mpr
    apply projectiveClass_eq_iff.mpr
    refine ⟨lam, hlam0, ?_⟩
    change Kernel.mul (Kernel.mul D.matrix (R : AMat)) D.inverse = lam • phase s
    rw [hR]
    exact hnorm
  refine ⟨q, D, su, hq, hD, hconf, heq, ?_⟩
  rw [← phaseHom_order, ← heq]
  simpa only [MulAut.conj_apply] using
    (MulAut.conj (pglMk _ (basisGL D))).orderOf_eq (pglMk _ R)

end
end Paper2.HeightOne.GroupSplit
