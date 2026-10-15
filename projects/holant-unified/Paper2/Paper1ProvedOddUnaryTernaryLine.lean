import Paper2.Paper1ProvedOddUnaryTernaryW

/-! Three nonzero repeated W columns with all cyclic ordinary pairings
zero lie on one actual isotropic line. The proportionality scalars are
nonzero and the two coordinates of that line are nonzero. -/
namespace Paper2.Paper1Proved.OddUnary.TernaryW
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem common_isotropic_line
    (A B C : Holant.Tractable.InvertibleKernel)
    (bc : W.gram (1 : AlgebraicComplex) B.matrix C.matrix false false = 0)
    (ab : W.gram 1 A.matrix B.matrix false false = 0)
    (ca : W.gram 1 C.matrix A.matrix false false = 0) :
    A.matrix false false ≠ 0 ∧ A.matrix true false ≠ 0 ∧
      A.matrix false false ^ 2 + A.matrix true false ^ 2 = 0 ∧
      ∃ s t : AlgebraicComplex, s ≠ 0 ∧ t ≠ 0 ∧
        (∀ v, B.matrix v false = s * A.matrix v false) ∧
        (∀ v, C.matrix v false = t * A.matrix v false) := by
  have da := Holant.Tractable.SymmetricBinaryPullback.determinant_ne_zero A
  have db := Holant.Tractable.SymmetricBinaryPullback.determinant_ne_zero B
  have dc := Holant.Tractable.SymmetricBinaryPullback.determinant_ne_zero C
  simp only [W.gram,one_mul] at bc ab ca
  simp only [Holant.Tractable.SymmetricBinaryPullback.determinant] at da db dc
  have a0 : A.matrix false false ≠ 0 := by
    intro zero
    have a1 : A.matrix true false ≠ 0 := by
      intro z
      exact da (by rw [zero,z];ring)
    have b1 : B.matrix true false = 0 := by
      have h : A.matrix true false * B.matrix true false = 0 := by simpa [zero] using ab
      exact (mul_eq_zero.mp h).resolve_left a1
    have c1 : C.matrix true false = 0 := by
      have h : C.matrix true false * A.matrix true false = 0 := by simpa [zero] using ca
      exact (mul_eq_zero.mp h).resolve_right a1
    have b0 : B.matrix false false ≠ 0 := by
      intro z
      exact db (by rw [z,b1];ring)
    have c0 : C.matrix false false ≠ 0 := by
      intro z
      exact dc (by rw [z,c1];ring)
    exact (mul_ne_zero b0 c0) (by simpa [b1,c1] using bc)
  have a1 : A.matrix true false ≠ 0 := by
    intro zero
    have b0 : B.matrix false false = 0 := by
      have h : A.matrix false false * B.matrix false false = 0 := by simpa [zero] using ab
      exact (mul_eq_zero.mp h).resolve_left a0
    have c0 : C.matrix false false = 0 := by
      have h : C.matrix false false * A.matrix false false = 0 := by simpa [zero] using ca
      exact (mul_eq_zero.mp h).resolve_right a0
    have b1 : B.matrix true false ≠ 0 := by
      intro z
      exact db (by rw [b0,z];ring)
    have c1 : C.matrix true false ≠ 0 := by
      intro z
      exact dc (by rw [c0,z];ring)
    exact (mul_ne_zero b1 c1) (by simpa [b0,c0] using bc)
  have b0 : B.matrix false false ≠ 0 := by
    intro zero
    have b1 : B.matrix true false = 0 := by
      have h : A.matrix true false * B.matrix true false = 0 := by simpa [zero] using ab
      exact (mul_eq_zero.mp h).resolve_left a1
    exact db (by rw [zero,b1];ring)
  have c0 : C.matrix false false ≠ 0 := by
    intro zero
    have c1 : C.matrix true false = 0 := by
      have h : C.matrix true false * A.matrix true false = 0 := by simpa [zero] using ca
      exact (mul_eq_zero.mp h).resolve_right a1
    exact dc (by rw [zero,c1];ring)
  have isotropic : A.matrix false false ^ 2 + A.matrix true false ^ 2 = 0 := by
    have h : (A.matrix false false ^ 2 + A.matrix true false ^ 2) *
        B.matrix false false * C.matrix false false = 0 := by
      linear_combination A.matrix true false ^ 2 * bc + A.matrix false false * C.matrix false false * ab -
        A.matrix true false * B.matrix true false * ca
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right c0)).resolve_right b0
  have crossB : A.matrix true false * B.matrix false false = A.matrix false false * B.matrix true false := by
    have h : A.matrix true false *
        (A.matrix true false * B.matrix false false - A.matrix false false * B.matrix true false) = 0 := by
      linear_combination B.matrix false false * isotropic - A.matrix false false * ab
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left a1)
  have crossC : A.matrix true false * C.matrix false false = A.matrix false false * C.matrix true false := by
    have h : A.matrix true false *
        (A.matrix true false * C.matrix false false - A.matrix false false * C.matrix true false) = 0 := by
      linear_combination C.matrix false false * isotropic - A.matrix false false * ca
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left a1)
  refine ⟨a0,a1,isotropic,B.matrix false false / A.matrix false false,
    C.matrix false false / A.matrix false false,div_ne_zero b0 a0,div_ne_zero c0 a0,?_,?_⟩
  · intro v
    cases v
    · exact (div_mul_cancel₀ _ a0).symm
    · field_simp [a0]
      simpa only [mul_comm] using crossB.symm
  · intro v
    cases v
    · exact (div_mul_cancel₀ _ a0).symm
    · field_simp [a0]
      simpa only [mul_comm] using crossC.symm

end
end Paper2.Paper1Proved.OddUnary.TernaryW

