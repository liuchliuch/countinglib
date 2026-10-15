import Paper2.HeightOne.GroupSplit.Source

/-! Literal Walsh analysis of actual native binary contraction kernels. Walsh
matrices are analytic coordinates only, never a legal GO(X) normalization. -/
namespace Paper2.HeightOne.PhaseCards
open Tractable GroupSplit GroupSplit.MatrixGroup
open GroupSplit.FiniteGroupFacts.ProjectiveCentralizers
noncomputable section

/-- The source's unnormalized Walsh matrix P. -/
def walsh : AMat := fun i j => if i && j then -1 else 1

def walshInv : AMat := (1 / 2 : AlgebraicComplex) • walsh

def plusKernel (s : AlgebraicComplex) : AMat :=
  fun i j => if i = j then (if i then -s else 1) else 0

def minusKernel (s : AlgebraicComplex) : AMat :=
  fun i j => if i = j then 0 else (if i then -s else 1)

def reflectedBinary (s : AlgebraicComplex) : AMat :=
  fun i j => if i = j then 0 else (if i then 1 else -s)

/-- Two native X edges, one on each ordered end of the actual binary. -/
def nativeKernel (B : AMat) : AMat := X * B * X

/-- P is used only for the bilinear coordinate calculation at the two deleted ports. -/
def analysisKernel (B : AMat) : AMat := walsh.transpose * nativeKernel B * walsh

/-- The binary signature itself in P⁻¹ coordinates. -/
def walshBinary (B : AMat) : AMat := walshInv * B * walshInv.transpose

lemma walsh_transpose : walsh.transpose = walsh := by
  funext i j
  cases i <;> cases j <;> rfl

lemma walshInv_mul_walsh : walshInv * walsh = 1 := by
  funext i j
  cases i <;> cases j <;> norm_num [walshInv, walsh, Matrix.mul_apply]

lemma walsh_mul_walshInv : walsh * walshInv = 1 := by
  funext i j
  cases i <;> cases j <;> norm_num [walshInv, walsh, Matrix.mul_apply]

lemma walsh_native_edge : walsh.transpose * X * walsh = (2 : AlgebraicComplex) • (zGL : AMat) := by
  funext i j
  cases i <;> cases j <;>
    norm_num [walsh, X, zGL, diagonalGL, diagonal, Matrix.mul_apply, Signature.disequality]

lemma matrix_of_transfer {B T : AMat} {c : AlgebraicComplex}
    (h : transfer B = c • T) : B = c • (T * X) := by
  calc
    B = transfer B * X := by simp only [transfer, Matrix.mul_assoc, X_mul_X, Matrix.mul_one]
    _ = c • (T * X) := by rw [h, Matrix.smul_mul]

/-- A chosen rotation representative yields exactly 2c K⁺_s, recording the
nonzero representative scale c and the source's factor two. -/
theorem rotation_analysis_kernel {B : AMat} {c s : AlgebraicComplex}
    (h : transfer B = c • phase s) : analysisKernel B = (2 * c) • plusKernel s := by
  rw [matrix_of_transfer h]
  funext i j
  cases i <;> cases j <;>
    simp [analysisKernel, nativeKernel, walsh, X, Signature.disequality,
      phase, balanced, plusKernel, Matrix.mul_apply, Matrix.smul_apply] <;> field_simp <;> ring

/-- Reversing the actual reflection representative yields -2c K⁻_s. The sign
is part of the recorded nonzero scalar, and the phase is unchanged. -/
theorem reflection_reversed_analysis_kernel {B : AMat} {c s : AlgebraicComplex}
    (h : transfer B = c • ((zGL : AMat) * phase s)) :
    analysisKernel B.transpose = (-2 * c) • minusKernel s := by
  rw [matrix_of_transfer h]
  funext i j
  cases i <;> cases j <;>
    simp [analysisKernel, nativeKernel, walsh, X, Signature.disequality,
      zGL, diagonalGL, diagonal, phase, balanced, minusKernel,
      Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply] <;> field_simp <;> ring

lemma rotation_walsh_binary {B : AMat} {c s : AlgebraicComplex}
    (h : transfer B = c • phase s) : walshBinary B = (c / 2) • plusKernel s := by
  rw [matrix_of_transfer h]
  funext i j
  cases i <;> cases j <;>
    simp [walshBinary, walshInv, walsh, X, Signature.disequality,
      phase, balanced, plusKernel, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.transpose_apply] <;> field_simp <;> ring

lemma reflection_walsh_binary {B : AMat} {c s : AlgebraicComplex}
    (h : transfer B = c • ((zGL : AMat) * phase s)) :
    walshBinary B = (c / 2) • reflectedBinary s := by
  rw [matrix_of_transfer h]
  funext i j
  cases i <;> cases j <;>
    simp [walshBinary, walshInv, walsh, X, Signature.disequality,
      zGL, diagonalGL, diagonal, phase, balanced, reflectedBinary,
      Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply] <;> field_simp <;> ring

end
end Paper2.HeightOne.PhaseCards
