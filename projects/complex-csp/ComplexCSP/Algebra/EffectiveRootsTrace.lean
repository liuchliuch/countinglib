import Mathlib.RingTheory.Trace.Basic
import Mathlib.Analysis.Polynomial.CauchyBound
import ComplexCSP.Algebra.NumberFieldTorsion

/-!
# Trace-box foundations for exact root-of-unity enumeration

The finite candidate set is derived from trace integrality, an embedding bound,
and the invertible trace Gram matrix. No hypothesis that an enumeration already
contains the roots of unity is used. The natural embedding bound is supplied
here as an intermediate input and is discharged from integer polynomials in a
separate module.
-/

namespace ComplexCSP.EffectiveRoots

open scoped BigOperators Matrix

/-- A computable rational matrix inverse, using adjugate and determinant.
Unlike mathlib's general `Matrix.inv`, no classical unit choice is needed. -/
def rationalInverse {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  M.det⁻¹ • M.adjugate

theorem rationalInverse_mul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.det ≠ 0) :
    rationalInverse M * M = 1 := by
  rw [rationalInverse, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul,
    inv_mul_cancel₀ hM, one_smul]

/-- A finite executable box of integer trace vectors. -/
def integerTraceBox (n R : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun i ↦ Finset.Icc (-((n * R ^ i.val : ℕ) : ℤ)) ((n * R ^ i.val : ℕ) : ℤ))

/-- Executable rational coordinate candidates, given the rational trace Gram
matrix and an integer bound on all conjugates of the integral generator. -/
def candidateCoordinates {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (R : ℕ) :
    Finset (Fin n → ℚ) :=
  (integerTraceBox n R).image (fun t ↦ (rationalInverse M).mulVec (fun i ↦ (t i : ℚ)))

variable {K : Type*} [Field K] [NumberField K]

noncomputable def traceVector (pb : PowerBasis ℚ K) (z : K) : Fin pb.dim → ℚ :=
  fun i ↦ Algebra.trace ℚ K (z * pb.gen ^ i.val)

noncomputable def traceGram (pb : PowerBasis ℚ K) : Matrix (Fin pb.dim) (Fin pb.dim) ℚ :=
  fun i j ↦ Algebra.trace ℚ K (pb.gen ^ (i.val + j.val))

theorem traceGram_eq_traceMatrix (pb : PowerBasis ℚ K) :
    traceGram pb = Algebra.traceMatrix ℚ pb.basis := by
  ext i j
  simp only [traceGram, Algebra.traceMatrix_apply, Algebra.traceForm_apply, pb.basis_eq_pow, pow_add]

theorem traceGram_det_ne_zero (pb : PowerBasis ℚ K) : (traceGram pb).det ≠ 0 := by
  rw [traceGram_eq_traceMatrix]
  exact det_traceMatrix_ne_zero' pb

theorem traceGram_mul_coordinates (pb : PowerBasis ℚ K) (z : K) :
    (traceGram pb).mulVec (pb.basis.equivFun z) = traceVector pb z := by
  change _ = fun i : Fin pb.dim ↦ Algebra.trace ℚ K (z * pb.gen ^ i.val)
  rw [traceGram_eq_traceMatrix, Algebra.traceMatrix_of_basis_mulVec]
  simp only [pb.basis_eq_pow]

/-- Rational coordinates are recovered exactly from the integer trace vector. -/
theorem reconstruct_coordinates (pb : PowerBasis ℚ K) (z : K) :
    (rationalInverse (traceGram pb)).mulVec (traceVector pb z) = pb.basis.equivFun z := by
  rw [← traceGram_mul_coordinates, Matrix.mulVec_mulVec,
    rationalInverse_mul _ (traceGram_det_ne_zero pb), Matrix.one_mulVec]

theorem traceVector_injective (pb : PowerBasis ℚ K) : Function.Injective (traceVector pb) := by
  intro x y h
  apply pb.basis.equivFun.injective
  rw [← reconstruct_coordinates pb x, ← reconstruct_coordinates pb y, h]

/-- Products of roots of unity with integral generator powers have integer
rational trace. -/
theorem traceVector_is_integer (pb : PowerBasis ℚ K) (hgen : IsIntegral ℤ pb.gen)
    (ζ : K) (hζ : IsOfFinOrder ζ) (i : Fin pb.dim) :
    ∃ t : ℤ, (t : ℚ) = traceVector pb ζ i := by
  apply IsIntegrallyClosed.isIntegral_iff.mp
  exact Algebra.isIntegral_trace
    ((RowDetector.isIntegral_int_of_isOfFinOrder ζ hζ).mul (hgen.pow i.val))

/-- The trace embedding formula gives a uniform explicit bound for root-of-unity
trace coordinates. -/
theorem norm_traceVector_le (pb : PowerBasis ℚ K) (R : ℕ)
    (hR : ∀ σ : K →ₐ[ℚ] ℂ, ‖σ pb.gen‖ ≤ R)
    (ζ : K) (hζ : IsOfFinOrder ζ) (i : Fin pb.dim) :
    ‖(traceVector pb ζ i : ℂ)‖ ≤ (pb.dim : ℝ) * (R : ℝ) ^ i.val := by
  classical
  change ‖algebraMap ℚ ℂ (Algebra.trace ℚ K (ζ * pb.gen ^ i.val))‖ ≤ _
  rw [trace_eq_sum_embeddings ℂ]
  calc
    ‖∑ σ : K →ₐ[ℚ] ℂ, σ (ζ * pb.gen ^ i.val)‖ ≤
        ∑ σ : K →ₐ[ℚ] ℂ, ‖σ (ζ * pb.gen ^ i.val)‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : K →ₐ[ℚ] ℂ, (R : ℝ) ^ i.val := by
      apply Finset.sum_le_sum
      intro σ _
      have hn : ‖σ ζ‖ = 1 := (σ.toMonoidHom.isOfFinOrder hζ).norm_eq_one
      rw [map_mul, map_pow, norm_mul, norm_pow, hn, one_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) (hR σ) _
    _ = (pb.dim : ℝ) * (R : ℝ) ^ i.val := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, AlgHom.card, pb.finrank]

/-- Every root-of-unity trace vector occurs in the explicitly enumerated integer
box; this follows from integrality and the embedding estimate. -/
theorem traceVector_in_integerBox (pb : PowerBasis ℚ K) (hgen : IsIntegral ℤ pb.gen)
    (R : ℕ) (hR : ∀ σ : K →ₐ[ℚ] ℂ, ‖σ pb.gen‖ ≤ R)
    (ζ : K) (hζ : IsOfFinOrder ζ) :
    ∃ t ∈ integerTraceBox pb.dim R, (fun i ↦ (t i : ℚ)) = traceVector pb ζ := by
  classical
  choose t ht using traceVector_is_integer pb hgen ζ hζ
  refine ⟨t, ?_, funext ht⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  have hbound := norm_traceVector_le pb R hR ζ hζ i
  rw [← ht i] at hbound
  simp only [Rat.cast_intCast, Complex.norm_intCast] at hbound
  have habs : |t i| ≤ ((pb.dim * R ^ i.val : ℕ) : ℤ) := by exact_mod_cast hbound
  exact abs_le.mp habs

/-- The explicit rational candidates contain every root of unity's coordinates.
This is proved, rather than assumed as an input completeness condition. -/
theorem root_coordinates_mem_candidates (pb : PowerBasis ℚ K) (hgen : IsIntegral ℤ pb.gen)
    (R : ℕ) (hR : ∀ σ : K →ₐ[ℚ] ℂ, ‖σ pb.gen‖ ≤ R)
    (ζ : K) (hζ : IsOfFinOrder ζ) :
    pb.basis.equivFun ζ ∈ candidateCoordinates (traceGram pb) R := by
  classical
  obtain ⟨t, ht, hvec⟩ := traceVector_in_integerBox pb hgen R hR ζ hζ
  apply Finset.mem_image.mpr
  exact ⟨t, ht, by rw [hvec, reconstruct_coordinates]⟩

/-- Every cyclic power is a candidate, so the order is bounded by the actual
finite rational candidate-set cardinality. -/
theorem root_order_le_candidate_card (pb : PowerBasis ℚ K) (hgen : IsIntegral ℤ pb.gen)
    (R : ℕ) (hR : ∀ σ : K →ₐ[ℚ] ℂ, ‖σ pb.gen‖ ≤ R)
    (ζ : K) (hζ : IsOfFinOrder ζ) :
    orderOf ζ ≤ (candidateCoordinates (traceGram pb) R).card := by
  apply Finset.le_card_of_inj_on_range (fun n ↦ pb.basis.equivFun (ζ ^ n))
  · intro n _
    exact root_coordinates_mem_candidates pb hgen R hR (ζ ^ n) hζ.pow
  · intro i hi j hj hij
    exact pow_injOn_Iio_orderOf hi hj (pb.basis.equivFun.injective hij)

/-- An explicit factorial exponent kills every root of unity. Its definition
uses the finite trace-box enumeration and rational arithmetic only. -/
def candidateExponent {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (R : ℕ) : ℕ :=
  (candidateCoordinates M R).card.factorial

theorem root_pow_candidateExponent (pb : PowerBasis ℚ K) (hgen : IsIntegral ℤ pb.gen)
    (R : ℕ) (hR : ∀ σ : K →ₐ[ℚ] ℂ, ‖σ pb.gen‖ ≤ R)
    (ζ : K) (hζ : IsOfFinOrder ζ) : ζ ^ candidateExponent (traceGram pb) R = 1 := by
  apply orderOf_dvd_iff_pow_eq_one.mp
  exact Nat.dvd_factorial hζ.orderOf_pos (root_order_le_candidate_card pb hgen R hR ζ hζ)

end ComplexCSP.EffectiveRoots
