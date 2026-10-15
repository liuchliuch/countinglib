import Paper2.ExactInput.CoordinateOutputBound
import Mathlib.Algebra.Order.Floor.Ring

/-! The actual complex output has singly exponential magnitude in original graph
bits. Constants depend only on the fixed family/basis; no floating point is used. -/
namespace Paper2.ExactInput
open Paper2.Algebraic Paper2.Tractable Paper2.Problem
open scoped BigOperators

noncomputable def complexEmbedding (L : Language) : L.coefficientField →ₐ[ℚ] ℂ :=
  (algebraicClosure ℚ ℂ).val.comp L.coefficientField.val

noncomputable def basisMagnitudeBound (L : Language) : ℕ :=
  ⌈∑ i, ‖complexEmbedding L (L.fieldPresentation.basis i)‖⌉₊

lemma rational_norm_le_numerator (q : ℚ) : ‖(q : ℂ)‖ ≤ (q.num.natAbs : ℝ) := by
  rw [Rat.cast_def, norm_div, Complex.norm_intCast, Complex.norm_natCast]
  rw [Nat.cast_natAbs, Int.cast_abs]
  apply div_le_self (by positivity)
  exact_mod_cast q.den_pos

/-- Coordinates with B-bit canonical numerators have complex magnitude at most
one fixed basis constant times 2^B. Denominators are at least one. -/
theorem coordinates_norm_le (L : Language) (v : Fin (Module.finrank ℚ L.coefficientField) → ℚ)
    (B : ℕ) (hv : ∀ i, (v i).num.natAbs.size ≤ B) :
    ‖complexEmbedding L (L.fieldPresentation.decode v)‖ ≤ basisMagnitudeBound L * (2 : ℝ) ^ B := by
  have hc : ∀ i, ‖((v i : ℚ) : ℂ)‖ ≤ (2 : ℝ) ^ B := by
    intro i
    apply (rational_norm_le_numerator _).trans
    have h := (Nat.size_le.mp (hv i)).le
    exact_mod_cast h
  have hsum : (∑ i, ‖complexEmbedding L (L.fieldPresentation.basis i)‖) ≤ basisMagnitudeBound L :=
    Nat.le_ceil _
  rw [show L.fieldPresentation.decode v = ∑ i, v i • L.fieldPresentation.basis i from
    L.fieldPresentation.basis.equivFun_symm_apply v, map_sum]
  calc
    ‖∑ i, complexEmbedding L (v i • L.fieldPresentation.basis i)‖ ≤
        ∑ i, ‖complexEmbedding L (v i • L.fieldPresentation.basis i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖((v i : ℚ) : ℂ)‖ * ‖complexEmbedding L (L.fieldPresentation.basis i)‖ := by
      apply Finset.sum_congr rfl
      intro i _
      simp [map_smul, Algebra.smul_def, norm_mul]
    _ ≤ ∑ i, (2 : ℝ) ^ B * ‖complexEmbedding L (L.fieldPresentation.basis i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)
    _ = (2 : ℝ) ^ B * ∑ i, ‖complexEmbedding L (L.fieldPresentation.basis i)‖ := by
      rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ B * basisMagnitudeBound L := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := mul_comm _ _

/-- Quantified bound on the literal Holant value, in the same original input length
used by the finite-machine complexity interface. -/
theorem value_norm_le (w : Wiring) (L : Language) (G : Instance L) :
    ‖(value w L G : ℂ)‖ ≤ basisMagnitudeBound L *
      (2 : ℝ) ^ ((coordinateOutputPolynomial w L).eval ((inputEncoding L).encode G).length) := by
  have hc := coordinates_norm_le L (outputCoordinates w L G)
    ((coordinateOutputPolynomial w L).eval ((inputEncoding L).encode G).length)
    (fun i => (output_coordinate_num_den_bits w L G i).1)
  have he : complexEmbedding L (L.fieldPresentation.decode (outputCoordinates w L G)) =
      (value w L G : ℂ) :=
    congrArg (fun z : AlgebraicComplex => (z : ℂ)) (outputCoordinates_spec w L G)
  rwa [he] at hc

end Paper2.ExactInput
