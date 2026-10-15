import Paper2.ExactInput.FixedRootCodec.ReverseFieldLattice
import Paper2.ExactInput.FixedRootCodec.ReverseRounding
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Fixed conjugate coordinates for the inverse codec. All embeddings and the
inverse matrix depend only on the fixed field basis. Enumerating assignments
of the at most d roots of an input polynomial uses d^n cases, a constant for
this fixed field. The mathematical recovery below supplies no varying-root
isolation oracle and asserts no complete decoder machine. -/
namespace Paper2.ExactInput.FixedRootCodec
open Paper2.Algebraic Polynomial Matrix
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] {n : ℕ}

def embeddingEnumeration (F : FixedField K n) : Fin n ≃ (K →ₐ[ℚ] ℂ) :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin,AlgHom.card]
    simpa using (Module.finrank_eq_card_basis F.basis).symm)

def fieldEmbeddingMatrix (F : FixedField K n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => embeddingEnumeration F i (F.basis j)

theorem fieldEmbeddingMatrix_transpose (F : FixedField K n) :
    (fieldEmbeddingMatrix F).transpose =
      Algebra.embeddingsMatrixReindex ℚ ℂ F.basis (embeddingEnumeration F) := by
  ext i j
  simp [fieldEmbeddingMatrix,Algebra.embeddingsMatrixReindex,Algebra.embeddingsMatrix]

theorem fieldEmbeddingMatrix_det_ne_zero (F : FixedField K n) :
    (fieldEmbeddingMatrix F).det ≠ 0 := by
  have ht : (Algebra.traceMatrix ℚ F.basis).det ≠ 0 := by
    rw [Algebra.traceMatrix_of_basis]
    exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero F.basis).mp
      (traceForm_nondegenerate ℚ K)
  have he := Algebra.traceMatrix_eq_embeddingsMatrixReindex_mul_trans ℚ ℂ
    F.basis (embeddingEnumeration F)
  rw [← fieldEmbeddingMatrix_transpose] at he
  have hd := congrArg Matrix.det he
  rw [← RingHom.mapMatrix_apply,← RingHom.map_det,Matrix.det_mul,
    Matrix.det_transpose,Matrix.transpose_transpose] at hd
  intro hz
  rw [hz,mul_zero] at hd
  exact ht ((algebraMap ℚ ℂ).injective (hd.trans (map_zero _).symm))

def inverseFieldEmbeddingMatrix (F : FixedField K n) := (fieldEmbeddingMatrix F)⁻¹

def conjugateValues (F : FixedField K n) (x : K) : Fin n → ℂ :=
  fun i => embeddingEnumeration F i x

theorem fieldEmbeddingMatrix_coordinates (F : FixedField K n) (x : K) :
    fieldEmbeddingMatrix F *ᵥ (fun i => (F.basis.repr x i : ℂ)) = conjugateValues F x := by
  funext i
  have h := congrArg (embeddingEnumeration F i) (F.basis.sum_repr x)
  simpa [fieldEmbeddingMatrix,Matrix.mulVec,dotProduct,conjugateValues,
    map_sum,Algebra.smul_def,mul_comm] using h

theorem inverseFieldEmbeddingMatrix_recovers (F : FixedField K n) (x : K) :
    inverseFieldEmbeddingMatrix F *ᵥ conjugateValues F x =
      (fun i => (F.basis.repr x i : ℂ)) := by
  rw [← fieldEmbeddingMatrix_coordinates,inverseFieldEmbeddingMatrix,
    Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (fieldEmbeddingMatrix_det_ne_zero F)),Matrix.one_mulVec]

/-- Every conjugate of the selected field element is one of the listed roots.
The same root can occur at multiple embeddings when x generates a subfield. -/
theorem conjugate_assignment_exists (F : FixedField K n) {d : ℕ}
    (p : ℚ[X]) (roots : Fin d → ℂ)
    (cover : ∀ z : ℂ, p.aeval z = 0 → ∃ j,roots j = z)
    (x : K) (hx : p.aeval x = 0) :
    ∃ assignment : Fin n → Fin d,
      (fun i => roots (assignment i)) = conjugateValues F x := by
  have h : ∀ i : Fin n,∃ j,roots j = conjugateValues F x i := by
    intro i
    apply cover
    change p.aeval (embeddingEnumeration F i x) = 0
    rw [Polynomial.aeval_algHom_apply,hx,map_zero]
  choose assignment ha using h
  exact ⟨assignment,funext ha⟩

theorem conjugate_assignment_card (n d : ℕ) : Fintype.card (Fin n → Fin d) = d^n := by
  simp

/-- Lattice rounding recovers all exact field coordinates once the approximate
inverse-matrix row has strict half-unit accuracy at the explicit denominator. -/
theorem rounded_coordinates_recover (F : FixedField K n) (D : ℕ) (hD : 0 < D)
    (x : K) (hx : IsIntegral ℤ ((D : K) * x)) (q : Fin n → ℚ)
    (accuracy : ∀ i, |q i - F.basis.repr x i| <
      1 / (2 * (coordinateLatticeDenominator F * D : ℕ) : ℚ)) :
    (fun i => latticeRound (coordinateLatticeDenominator F * D) (q i)) =
      (fun i => F.basis.repr x i) := by
  funext i
  obtain ⟨a,ha⟩ := coordinates_on_lattice F D hD x hx i
  have hd : 0 < coordinateLatticeDenominator F * D :=
    Nat.mul_pos (coordinateLatticeDenominator_pos F) hD
  have hdQ : (0 : ℚ) < (coordinateLatticeDenominator F * D : ℕ) := by exact_mod_cast hd
  rw [ha]
  apply latticeRound_correct _ _ a hd
  have h := accuracy i
  rw [ha] at h
  have hm := mul_lt_mul_of_pos_left h hdQ
  have hm' : |(coordinateLatticeDenominator F * D : ℕ) *
      (q i - (a : ℚ) / (coordinateLatticeDenominator F * D : ℕ))| <
      (coordinateLatticeDenominator F * D : ℕ) *
      (1 / (2 * (coordinateLatticeDenominator F * D : ℕ) : ℚ)) := by
    simpa only [abs_mul,abs_of_pos hdQ] using hm
  have he : (coordinateLatticeDenominator F * D : ℕ) *
      (q i - (a : ℚ) / (coordinateLatticeDenominator F * D : ℕ)) =
      (coordinateLatticeDenominator F * D : ℕ) * q i - a := by
    field_simp [ne_of_gt hdQ]
  rw [he] at hm'
  have hc : (coordinateLatticeDenominator F * D : ℕ) *
      (1 / (2 * (coordinateLatticeDenominator F * D : ℕ) : ℚ)) = 1/2 := by
    field_simp [ne_of_gt hdQ]
  simpa only [hc] using hm'

end
end Paper2.ExactInput.FixedRootCodec
