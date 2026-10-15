import ComplexCSP.Algebra.EncodedNumberField
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ComplexCSP.Algebra.EffectiveRootsTrace

/-! # Executable rational-vector inversion

The multiplication matrix, adjugate, determinant, and rational divisions are all
finite computations from the input relation and vector. Inversion branches on
rational coordinate equality, not on a classical decision in the semantic field.
-/
namespace ComplexCSP.EncodedNumberField
open scoped BigOperators

/-- The matrix whose j-th column is multiplication of the j-th basis vector. -/
def multiplicationMatrix {n : ℕ} (c a : CoeffVector n) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => mul c a (unitVector j) i

/-- Fully finite inverse calculation. Invalid relation data still yield a total
rational calculation; correctness below requires the actual root/basis evidence. -/
def inverse {n : ℕ} (c a : CoeffVector n) : CoeffVector n :=
  if equal a (zero n) then zero n else
    (EffectiveRoots.rationalInverse (multiplicationMatrix c a)).mulVec (one n)

def divide {n : ℕ} (c a b : CoeffVector n) : CoeffVector n := mul c a (inverse c b)

section Interpretation
variable {K : Type*} [CommRing K] [Algebra ℚ K] {n : ℕ}

/-- Matrix action has the same interpretation as multiplication. -/
theorem interpret_multiplicationMatrix_mulVec (α : K) (c a b : CoeffVector n)
    (hc : α ^ n = interpret α c) :
    interpret α ((multiplicationMatrix c a).mulVec b) = interpret α a * interpret α b := by
  have he : (multiplicationMatrix c a).mulVec b = ∑ j, b j • mul c a (unitVector j) := by
    funext i
    simp [Matrix.mulVec, dotProduct, multiplicationMatrix, mul_comm]
  rw [he, interpret_sum]
  simp only [interpret_smul, interpret_mul α c a _ hc, interpret_unitVector]
  change (∑ j, algebraMap ℚ K (b j) * (interpret α a * α ^ j.val)) =
    interpret α a * (∑ j, algebraMap ℚ K (b j) * α ^ j.val)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring
end Interpretation

section PowerBasis
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The executable matrix agrees entrywise with the actual basis multiplication
matrix. Actual basis extraction is only on the specification side. -/
theorem multiplicationMatrix_eq_leftMulMatrix (pb : PowerBasis ℚ K)
    (c a : CoeffVector pb.dim) (hc : pb.gen ^ pb.dim = interpret pb.gen c) :
    multiplicationMatrix c a = Algebra.leftMulMatrix pb.basis (interpret pb.gen a) := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  have he : mul c a (unitVector j) = pb.basis.equivFun (interpret pb.gen a * pb.basis j) := by
    apply interpret_injective pb
    rw [interpret_mul _ _ _ _ hc, interpret_unitVector, interpret_coordinates, pb.basis_eq_pow]
  change mul c a (unitVector j) i = _
  rw [he]
  rfl

/-- A nonzero semantic element has a nonsingular executable multiplication matrix. -/
theorem multiplicationMatrix_det_ne_zero (pb : PowerBasis ℚ K)
    (c a : CoeffVector pb.dim) (hc : pb.gen ^ pb.dim = interpret pb.gen c)
    (ha : interpret pb.gen a ≠ 0) : (multiplicationMatrix c a).det ≠ 0 := by
  have hi : Function.Injective (multiplicationMatrix c a).mulVec := by
    intro u v huv
    apply interpret_injective pb
    apply mul_left_cancel₀ ha
    rw [← interpret_multiplicationMatrix_mulVec pb.gen c a u hc,
      ← interpret_multiplicationMatrix_mulVec pb.gen c a v hc, huv]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero

/-- Total executable inversion agrees with field inversion, including at zero. -/
theorem interpret_inverse (pb : PowerBasis ℚ K) (c a : CoeffVector pb.dim)
    (hc : pb.gen ^ pb.dim = interpret pb.gen c) :
    interpret pb.gen (inverse c a) = (interpret pb.gen a)⁻¹ := by
  by_cases he : equal a (zero pb.dim) = true
  · have ha : a = zero pb.dim := (equal_correct _ _).mp he
    simp [inverse, ha]
  · have ha : interpret pb.gen a ≠ 0 := by
      intro hz
      apply he
      apply (equal_correct _ _).mpr
      apply interpret_injective pb
      simpa only [interpret_zero] using hz
    have hd := multiplicationMatrix_det_ne_zero pb c a hc ha
    have hmat : (multiplicationMatrix c a).mulVec (inverse c a) = one pb.dim := by
      simp only [inverse, he, Bool.false_eq_true, ↓reduceIte, EffectiveRoots.rationalInverse]
      rw [Matrix.mulVec_mulVec, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul,
        inv_mul_cancel₀ hd, one_smul, Matrix.one_mulVec]
    have hm : interpret pb.gen a * interpret pb.gen (inverse c a) = 1 := by
      rw [← interpret_multiplicationMatrix_mulVec pb.gen c a _ hc, hmat]
      exact interpret_one pb.gen pb.dim_pos
    apply mul_left_cancel₀ ha
    rw [hm, mul_inv_cancel₀ ha]

/-- Total runtime rational-vector division has the usual field semantics. -/
theorem interpret_divide (pb : PowerBasis ℚ K) (c a b : CoeffVector pb.dim)
    (hc : pb.gen ^ pb.dim = interpret pb.gen c) :
    interpret pb.gen (divide c a b) = interpret pb.gen a / interpret pb.gen b := by
  rw [divide, interpret_mul _ _ _ _ hc, interpret_inverse pb c b hc, div_eq_mul_inv]
end PowerBasis

end ComplexCSP.EncodedNumberField
