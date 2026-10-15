import Paper2.HeightTwo
import Paper2.Tractable.Conformal
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Exact diagonal GO(X) repair of a nonsingular weighted equality. All roots
remain in the algebraic-complex input field; the transformed table is literal I,
with the native-edge multiplier recorded explicitly. -/
namespace Paper2.HeightTwo
open Tractable
noncomputable section

lemma weightedEquality_table (f : Signature AlgebraicComplex 2)
    (hf : WeightedEquality f) :
    f = kernelSignature (diagonalKernel (f ![false, false]) (f ![true, true])) := by
  funext x
  have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
  rw [hx]
  rcases hf with ⟨h01, h10, _, _⟩
  cases hx0 : x 0 <;> cases hx1 : x 1 <;>
    simp [kernelSignature, diagonalKernel, h01, h10]

/-- Explicit inverse, retaining both nonzero square roots. -/
def diagonalBasis (a b : AlgebraicComplex) (ha : a ≠ 0) (hb : b ≠ 0) :
    InvertibleKernel where
  matrix := diagonalKernel a b
  inverse := diagonalKernel a⁻¹ b⁻¹
  matrix_inverse := by
    funext x y
    cases x <;> cases y <;> simp [Kernel.mul_apply, diagonalKernel, Signature.equality, ha, hb]
  inverse_matrix := by
    funext x y
    cases x <;> cases y <;> simp [Kernel.mul_apply, diagonalKernel, Signature.equality, ha, hb]

lemma diagonalBasis_pullback (a b : AlgebraicComplex) (ha : a ≠ 0) (hb : b ≠ 0) :
    Kernel.pullback Signature.disequality (diagonalBasis a b ha hb).matrix =
      fun x y => (a * b) * Signature.disequality x y := by
  funext x y
  cases x <;> cases y <;>
    simp [diagonalBasis, Kernel.pullback, Kernel.mul_apply, Kernel.transpose,
      diagonalKernel, Signature.disequality, mul_comm]

lemma diagonalBasis_conformal (a b : AlgebraicComplex) (ha : a ≠ 0) (hb : b ≠ 0) :
    XConformal (diagonalBasis a b ha hb) :=
  ⟨a * b, mul_ne_zero ha hb, diagonalBasis_pullback a b ha hb⟩

lemma diagonalBasis_normalizes (a b p q : AlgebraicComplex) (ha : a ≠ 0) (hb : b ≠ 0)
    (hp : a ^ 2 * p = 1) (hq : b ^ 2 * q = 1) :
    (diagonalBasis a b ha hb).action (kernelSignature (diagonalKernel p q)) =
      kernelSignature Signature.equality := by
  rw [InvertibleKernel.action, coordinateAction_kernelSignature]
  congr 1
  funext x y
  cases x <;> cases y <;>
    simp [diagonalBasis, Kernel.mul_apply, Kernel.transpose, diagonalKernel,
      Signature.equality] <;> first | linear_combination hp | linear_combination hq

lemma exists_inverse_square_root (p : AlgebraicComplex) (hp : p ≠ 0) :
    ∃ a : AlgebraicComplex, a ≠ 0 ∧ a ^ 2 * p = 1 := by
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq p⁻¹ (by decide : 0 < 2)
  refine ⟨a, ?_, ?_⟩
  · intro hz
    have : p⁻¹ = 0 := by rw [← ha, hz]; simp
    exact (inv_ne_zero hp) this
  · rw [ha]
    exact inv_mul_cancel₀ hp

/-- The source's normalization outputs literal binary equality, not a
proportional alias, and the same matrix belongs to the legal GO(X) group. -/
theorem weightedEquality_normalization (f : Signature AlgebraicComplex 2)
    (hf : WeightedEquality f) :
    ∃ D : InvertibleKernel, XConformal D ∧ D.action f = kernelSignature Signature.equality := by
  obtain ⟨a, ha, hpa⟩ := exists_inverse_square_root _ hf.2.2.1
  obtain ⟨b, hb, hqb⟩ := exists_inverse_square_root _ hf.2.2.2
  refine ⟨diagonalBasis a b ha hb, diagonalBasis_conformal a b ha hb, ?_⟩
  rw [weightedEquality_table f hf]
  exact diagonalBasis_normalizes a b _ _ ha hb hpa hqb

end
end Paper2.HeightTwo
