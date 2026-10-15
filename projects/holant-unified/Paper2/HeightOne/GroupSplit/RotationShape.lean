import Paper2.HeightOne.GroupSplit.Normalization

/-! A finite non-involutory rotation inverted by the distinguished Z has equal
diagonal entries and two nonzero off-diagonal entries. The unipotent exclusion
uses literal powers in characteristic zero. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.GroupSplit
open Tractable MatrixGroup
noncomputable section

def shear (t : AlgebraicComplex) : AMat := balanced 1 t 0

lemma shear_mul (s t : AlgebraicComplex) : shear s * shear t = shear (s + t) := by
  ext i j
  cases i <;> cases j <;> simp [shear, balanced, Matrix.mul_apply]

lemma shear_zero : shear 0 = 1 := by
  ext i j
  cases i <;> cases j <;> simp [shear, balanced]

lemma shear_pow (t : AlgebraicComplex) (n : ℕ) : shear t ^ n = shear ((n : AlgebraicComplex) * t) := by
  induction n with
  | zero => simp [shear_zero]
  | succ n ih =>
    rw [pow_succ, ih, shear_mul]
    congr 1
    push_cast
    ring

lemma finite_shear_trivial (t : AlgebraicComplex) (h : ProjectivelyFinite (shear t)) : t = 0 := by
  obtain ⟨n, hn, c, hc, he⟩ := h
  rw [shear_pow] at he
  have h01 := congrArg (fun M : AMat => M false true) he
  have ht : (n : AlgebraicComplex) * t = 0 := by
    simpa [shear, balanced, Matrix.smul_apply] using h01
  exact (mul_eq_zero.mp ht).resolve_left (Nat.cast_ne_zero.mpr hn.ne')

lemma finite_upper_balanced_trivial (a b : AlgebraicComplex)
    (ha : a ≠ 0) (h : ProjectivelyFinite (balanced a b 0)) : b = 0 := by
  have he : a⁻¹ • balanced a b 0 = shear (b / a) := by
    ext i j
    cases i <;> cases j <;>
      simp [shear, balanced, Matrix.smul_apply, ha, div_eq_mul_inv, mul_comm]
  have hs : ProjectivelyFinite (shear (b / a)) := he ▸ h.smul (inv_ne_zero ha)
  have hz := finite_shear_trivial _ hs
  exact (div_eq_zero_iff).mp hz |>.resolve_right ha

lemma projectivelyFinite_transpose {M : AMat} (h : ProjectivelyFinite M) :
    ProjectivelyFinite M.transpose := by
  obtain ⟨n, hn, c, hc, he⟩ := h
  refine ⟨n, hn, c, hc, ?_⟩
  rw [← Matrix.transpose_pow, he]
  simp

def zMatrix : AMat := fun i j => if i = j then (if i then -1 else 1) else 0

lemma zMatrix_sq : zMatrix * zMatrix = 1 := by
  ext i j
  cases i <;> cases j <;> simp [zMatrix, diagonalKernel, Matrix.mul_apply]

/-- This hypothesis is the literal scalar form of Z R Z = R⁻¹ in PGL.
The conclusion supplies precisely the matrix shape needed for legal normalization. -/
theorem rotation_balanced_shape (R : AMat) (hdet : Matrix.det R ≠ 0)
    (hfinite : ProjectivelyFinite R)
    (hinvolution : ¬ ∃ c : AlgebraicComplex, c ≠ 0 ∧ R ^ 2 = c • (1 : AMat))
    (hdihedral : ∃ c : AlgebraicComplex, c ≠ 0 ∧ zMatrix * R * zMatrix * R = c • (1 : AMat)) :
    ∃ a b c : AlgebraicComplex, b ≠ 0 ∧ c ≠ 0 ∧ R = balanced a b c := by
  obtain ⟨k, hk, he⟩ := hdihedral
  have hoff : R false true ≠ 0 ∨ R true false ≠ 0 := by
    by_contra! hz
    apply hinvolution
    refine ⟨k, hk, ?_⟩
    have hzR : zMatrix * R * zMatrix = R := by
      ext i j
      cases i <;> cases j <;>
        simp [zMatrix, diagonalKernel, Matrix.mul_apply, hz.1, hz.2]
    simpa only [hzR, pow_two] using he
  have hdiag : R false false = R true true := by
    rcases hoff with hb | hc
    · have hh := congrArg (fun M : AMat => M false true) he
      have hp : R false true * (R false false - R true true) = 0 := by
        simp [zMatrix, diagonalKernel, Matrix.mul_apply, Matrix.smul_apply] at hh
        linear_combination hh
      exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hb)
    · have hh := congrArg (fun M : AMat => M true false) he
      have hp : R true false * (R false false - R true true) = 0 := by
        simp [zMatrix, diagonalKernel, Matrix.mul_apply, Matrix.smul_apply] at hh
        linear_combination -hh
      exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hc)
  have hR : R = balanced (R false false) (R false true) (R true false) := by
    ext i j
    cases i <;> cases j <;> simp [balanced, hdiag]
  have hbc : R false true ≠ 0 ∧ R true false ≠ 0 := by
    have ha_if (hz : R true false = 0) : R false false ≠ 0 := by
      intro ha
      apply hdet
      rw [hR, balanced_det, ha, hz]
      simp
    have hc : R true false ≠ 0 := by
      intro hz
      have hbf : ProjectivelyFinite (balanced (R false false) (R false true) 0) := by
        have hf : ProjectivelyFinite (balanced (R false false) (R false true) (R true false)) := hR ▸ hfinite
        simpa only [hz] using hf
      have hb := finite_upper_balanced_trivial _ _ (ha_if hz) hbf
      exact hoff.elim (fun h => h hb) (fun h => h hz)
    have hb : R false true ≠ 0 := by
      intro hz
      have ha : R false false ≠ 0 := by
        intro ha
        apply hdet
        rw [hR, balanced_det, ha, hz]
        simp
      have ht : R.transpose = balanced (R false false) (R true false) 0 := by
        ext i j
        cases i <;> cases j <;> simp [Matrix.transpose_apply, balanced, hz, hdiag]
      have hcf := finite_upper_balanced_trivial _ _ ha
        (ht ▸ projectivelyFinite_transpose hfinite)
      exact hc hcf
    exact ⟨hb, hc⟩
  exact ⟨R false false, R false true, R true false, hbc.1, hbc.2, hR⟩

end
end Paper2.HeightOne.GroupSplit
