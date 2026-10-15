import Paper2.ExactInput.FixedRootCodec.ReverseCandidates
import Paper2.ExactInput.FixedRootCodec.VariableProjectionInput
import Mathlib.FieldTheory.Minpoly.Finite

/-! Public-descriptor bridges to the actual variable projection programs.
The Cartesian array deliberately retains all real/imaginary combinations;
the exact final verifier discards combinations that are not the selected root. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] {n : ℕ}

theorem rootDescriptor_field_degree (F : FixedField K n) (e : K →ₐ[ℚ] ℂ)
    (c : RootCode) (x : K) (hc : c.MinimalRepresents (e x)) :
    c.polynomial.natDegree≤n := by
  rw [RootCode.minimalRepresents_polynomial hc,
    minpoly.algHom_eq e (fun _ _ h => e.injective h)]
  have h := minpoly.natDegree_le (A := ℚ) x
  simpa only [Module.finrank_eq_card_basis F.basis,Fintype.card_fin] using h

theorem rootDescriptor_field_root (e : K →ₐ[ℚ] ℂ)
    (c : RootCode) (x : K) (hc : c.MinimalRepresents (e x)) :
    Polynomial.aeval x c.polynomial=0 := by
  apply e.injective
  change e (Polynomial.aeval x c.polynomial)=e 0
  rw [← Polynomial.aeval_algHom_apply e x c.polynomial,map_zero]
  exact hc.1.2.2.1

theorem rootDescriptor_conjugate_root (F : FixedField K n) (e : K →ₐ[ℚ] ℂ)
    (c : RootCode) (x : K) (hc : c.MinimalRepresents (e x)) (i : Fin n) :
    Polynomial.aeval (conjugateValues F x i) c.polynomial=0 := by
  change Polynomial.aeval (embeddingEnumeration F i x) c.polynomial=0
  rw [Polynomial.aeval_algHom_apply,rootDescriptor_field_root e c x hc,map_zero]

def rootRealProjection (n : ℕ) (c : RootCode) : Fin ((n+1)*(n+1)+1) → ℚ :=
  VariableProjection.realPolynomialCoefficients n (denseCoefficients (n+1) c.coefficients)

def rootImaginaryProjection (n : ℕ) (c : RootCode) : Fin (2*((n+1)*(n+1))+1) → ℚ :=
  VariableProjection.imaginaryPolynomialCoefficients n (denseCoefficients (n+1) c.coefficients)

def rootRealProjectionComputes (n : ℕ) :
    Computes rootEncoding (vectorEncoding ((n+1)*(n+1)+1)) (rootRealProjection n) :=
  (denseRootCoefficientsComputes (n+1)).andThen (VariableProjection.realPolynomialCoefficientsComputes n)

def rootImaginaryProjectionComputes (n : ℕ) :
    Computes rootEncoding (vectorEncoding (2*((n+1)*(n+1))+1)) (rootImaginaryProjection n) :=
  (denseRootCoefficientsComputes (n+1)).andThen (VariableProjection.imaginaryPolynomialCoefficientsComputes n)

def rootRecoveryRequestComputes (F : FixedField K n) :
    Computes rootEncoding UnaryBinary.unaryEncoding
      (fun c => inverseRecoveryPrecision F (sparseDenominator c.coefficients)+1) :=
  congrComputes ((rootDenominatorComputes.andThen (inverseRecoveryPrecisionComputes F)).andThen
    unarySuccessorComputes) (fun _ => rfl)

theorem rootProjection_ne_zero (n : ℕ) (c : RootCode) :
    VariablePolynomial.polynomial (rootRealProjection n c)≠0 ∧
      VariablePolynomial.polynomial (rootImaginaryProjection n c)≠0 :=
  VariableProjection.projection_vectors_ne_zero n _

theorem rootProjection_conjugate_cover (F : FixedField K n) (e : K →ₐ[ℚ] ℂ)
    (c : RootCode) (x : K) (hc : c.MinimalRepresents (e x)) (i : Fin n) :
    ((VariablePolynomial.polynomial (rootRealProjection n c)).map (algebraMap ℚ ℝ)).eval
        (conjugateValues F x i).re=0 ∧
      ((VariablePolynomial.polynomial (rootImaginaryProjection n c)).map (algebraMap ℚ ℝ)).eval
        (conjugateValues F x i).im=0 := by
  have heq := denseRootCoefficients_polynomial (n+1) c
    (Nat.lt_succ_of_le (rootDescriptor_field_degree F e c x hc))
  apply VariableProjection.projection_vectors_real_cover n
    (denseCoefficients (n+1) c.coefficients)
  · rw [heq]
    exact hc.1.1
  · rw [heq]
    exact rootDescriptor_conjugate_root F e c x hc i

def cartesianEnumeration (r s : ℕ) : Fin (r*s) ≃ (Fin r × Fin s) :=
  Fintype.equivOfCardEq (by simp)

def cartesianReal {r s : ℕ} (v : Fin r → ℚ) : Fin (r*s) → ℚ :=
  fun i => v (cartesianEnumeration r s i).1

def cartesianImaginary {r s : ℕ} (v : Fin s → ℚ) : Fin (r*s) → ℚ :=
  fun i => v (cartesianEnumeration r s i).2

def cartesianPointComputes (r s : ℕ) :
    Computes (pairEncoding (vectorEncoding r) (vectorEncoding s)) (conjugatePointEncoding (r*s))
      (fun p => (cartesianReal (s := s) p.1,cartesianImaginary (r := r) p.2)) := by
  let vr := Wiring.firstComputes (vectorEncoding r) (vectorEncoding s)
  let vi := Wiring.secondComputes (vectorEncoding r) (vectorEncoding s)
  exact pairComputes
    (assembleComputes _ (r*s) _ (fun i => vr.andThen (coordinateComputes r (cartesianEnumeration r s i).1)))
    (assembleComputes _ (r*s) _ (fun i => vi.andThen (coordinateComputes s (cartesianEnumeration r s i).2)))

theorem cartesianPoint_cover {r s : ℕ} (vr : Fin r → ℚ) (vi : Fin s → ℚ)
    (z : ℂ) (ε : ℝ) (hr : ∃ i, |(vr i : ℝ)-z.re|≤ε)
    (hi : ∃ j, |(vi j : ℝ)-z.im|≤ε) :
    ∃ k, ‖rationalComplexPoint (cartesianReal (s := s) vr)
      (cartesianImaginary (r := r) vi) k-z‖≤2*ε := by
  obtain ⟨i,hri⟩ := hr
  obtain ⟨j,hj⟩ := hi
  refine ⟨(cartesianEnumeration r s).symm (i,j),?_⟩
  have hn := Complex.norm_le_abs_re_add_abs_im
    (rationalComplexPoint (cartesianReal (s := s) vr)
      (cartesianImaginary (r := r) vi) ((cartesianEnumeration r s).symm (i,j))-z)
  simp only [rationalComplexPoint,cartesianReal,cartesianImaginary,Equiv.apply_symm_apply,
    Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.ratCast_re,Complex.ratCast_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,zero_mul,add_zero,zero_add,sub_zero] at hn
  have hp : |(vr i : ℝ)-z.re|+|(vi j : ℝ)-z.im|≤2*ε := by linarith
  simpa only [rationalComplexPoint,cartesianReal,cartesianImaginary,Equiv.apply_symm_apply] using
    hn.trans hp

theorem cartesianPoint_dyadic_cover {r s : ℕ} (vr : Fin r → ℚ) (vi : Fin s → ℚ)
    (z : ℂ) (k : ℕ) (hr : ∃ i, |(vr i : ℝ)-z.re|≤1/(2 : ℝ)^(k+1))
    (hi : ∃ j, |(vi j : ℝ)-z.im|≤1/(2 : ℝ)^(k+1)) :
    ∃ j, ‖rationalComplexPoint (cartesianReal (s := s) vr)
      (cartesianImaginary (r := r) vi) j-z‖≤1/(2 : ℝ)^k := by
  obtain ⟨j,hj⟩ := cartesianPoint_cover vr vi z (1/(2 : ℝ)^(k+1)) hr hi
  refine ⟨j,?_⟩
  convert hj using 1
  rw [pow_succ]
  field_simp

end
end Paper2.ExactInput.FixedRootCodec
