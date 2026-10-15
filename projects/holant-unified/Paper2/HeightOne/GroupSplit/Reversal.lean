import Paper2.HeightOne.GroupSplit.ActualTransfers
import Paper2.HeightOne.GroupSplit.ProjectiveCentralizers
import Paper2.HeightOne.GroupSplit.CompleteTransport

/-! The distinguished projective involution normalizes the complete actual group
because port reversal is an actual graph reindexing. -/
namespace Paper2.HeightOne.GroupSplit
open MatrixGroup Tractable FiniteGroupFacts.ProjectiveCentralizers
noncomputable section

lemma reversal_product (R : AMat) :
    reverseTransfer R * (zGL : AMat) * R * (zGL : AMat) = Matrix.det R • (1 : AMat) := by
  ext i j
  cases i <;> cases j <;>
    simp [reverseTransfer, X, zGL, diagonalGL, diagonal, Matrix.mul_apply,
      Matrix.transpose_apply, Signature.disequality, determinant_bool, Matrix.smul_apply] <;> ring

lemma reverseTransfer_det_ne_zero (U : Matrix.GeneralLinearGroup Bool AlgebraicComplex) :
    Matrix.det (reverseTransfer (U : AMat)) ≠ 0 := by
  unfold reverseTransfer
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero det_X_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero U)) det_X_ne_zero

def reversalGL (U : Matrix.GeneralLinearGroup Bool AlgebraicComplex) :
    Matrix.GeneralLinearGroup Bool AlgebraicComplex :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (reverseTransfer (U : AMat)) (reverseTransfer_det_ne_zero U)

lemma reversal_class (U : Matrix.GeneralLinearGroup Bool AlgebraicComplex) :
    pglMk _ (reversalGL U) = zClass * (pglMk _ U)⁻¹ * zClass := by
  have he : pglMk _ (reversalGL U) * zClass * pglMk _ U * zClass = 1 := by
    change pglMk _ (reversalGL U) * pglMk _ zGL * pglMk _ U * pglMk _ zGL = pglMk _ 1
    rw [← map_mul, ← map_mul, ← map_mul]
    apply pglMk_eq_iff_projectiveClass_eq.mpr
    apply projectiveClass_eq_iff.mpr
    exact ⟨Matrix.det (U : AMat), Matrix.GeneralLinearGroup.det_ne_zero U, reversal_product U⟩
  have hzInv : zClass⁻¹ = zClass := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using zClass_square)
  have h := congrArg (fun q => q * zClass * (pglMk _ U)⁻¹ * zClass) he
  simpa only [mul_assoc, ← pow_two zClass, zClass_square, one_mul, mul_one,
    mul_inv_cancel] using h

/-- Reversal plus inversion of the actual group yields normalization by Z. -/
theorem actualGroup_z_normalizes {F : SignatureFamily AlgebraicComplex}
    (hG : ProjectiveMatrixGroup (actualTransfers F)) :
    ∀ q ∈ projectiveSubgroup hG, zClass * q * zClass ∈ projectiveSubgroup hG := by
  intro q hq
  have hqi := (projectiveSubgroup hG).inv_mem hq
  obtain ⟨U, hU, hqU⟩ := hqi
  have hr : pglMk _ (reversalGL U) ∈ projectiveSubgroup hG :=
    ⟨reversalGL U, actualTransfers_reversal F U hU, rfl⟩
  rw [reversal_class, hqU, inv_inv] at hr
  exact hr

end
end Paper2.HeightOne.GroupSplit
