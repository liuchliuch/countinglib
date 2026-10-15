import Paper2.RelativeEO.AlgebraicARS
import Paper2.HeightOne.GroupSplit.Group

/-! Literal binary EO transfer arithmetic for Paper 2 Lemma 3.9. Positive
projective order gives equal coefficient moduli and an algebraic ARS scalar.
There is no complexity or local-descent assumption in these statements. -/
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup

noncomputable def eoMatrix (a b : AlgebraicComplex) : Binary (K := AlgebraicComplex) :=
  fun i j => if i then (if j then 0 else b) else (if j then a else 0)

noncomputable def matrixSignature (B : Binary (K := AlgebraicComplex)) : Signature AlgebraicComplex 2 :=
  fun x => B (x 0) (x 1)

noncomputable def eoSignature (a b : AlgebraicComplex) : Signature AlgebraicComplex 2 :=
  matrixSignature (eoMatrix a b)

theorem eo_transfer (a b : AlgebraicComplex) :
    transfer (eoMatrix a b) = Matrix.diagonal (fun i : Bool => if i then b else a) := by
  ext i j
  cases i <;> cases j <;>
    simp [transfer, eoMatrix, X, Matrix.mul_apply, Signature.disequality, Fintype.sum_bool]

/-- This is actual projective order: a positive matrix power is scalar identity. -/
theorem eo_projectivelyFinite_norm (a b : AlgebraicComplex)
    (h : ProjectivelyFinite (transfer (eoMatrix a b))) : ‖(a : ℂ)‖ = ‖(b : ℂ)‖ := by
  obtain ⟨r, hr, c, _, he⟩ := h
  rw [eo_transfer, Matrix.diagonal_pow] at he
  have ha : a ^ r = c := by simpa using congrArg (fun M => M false false) he
  have hb : b ^ r = c := by simpa using congrArg (fun M => M true true) he
  have hc : (a : ℂ) ^ r = (b : ℂ) ^ r := by exact_mod_cast ha.trans hb.symm
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hr.ne').mp
  simpa only [norm_pow] using congrArg norm hc

theorem eoMatrix_det_ne_zero (a b : AlgebraicComplex) (ha : a ≠ 0) (hb : b ≠ 0) :
    Matrix.det (eoMatrix a b) ≠ 0 := by
  have hd : Matrix.det (transfer (eoMatrix a b)) ≠ 0 := by
    rw [eo_transfer, Matrix.det_diagonal]
    simpa [Fintype.prod_bool] using mul_ne_zero hb ha
  exact (mul_ne_zero_iff.mp (by simpa only [transfer, Matrix.det_mul] using hd)).1

theorem eoSignature_ne_zero_left (a b : AlgebraicComplex) (ha : a ≠ 0) : eoSignature a b ≠ 0 := by
  intro hz
  have h := congrFun hz (fun i => i == 1)
  exact ha h

/-- Equal nonzero off-diagonal moduli are exactly what is needed to normalize
this algebraic EO binary to ARS. The scalar descent is the proved theorem above. -/
theorem eo_binary_algebraic_ars (a b : AlgebraicComplex) (ha : a ≠ 0) (hb : b ≠ 0)
    (hnorm : ‖(a : ℂ)‖ = ‖(b : ℂ)‖) :
    ∃ c : AlgebraicComplex, c ≠ 0 ∧ ∀ x,
      (c : ℂ)⁻¹ * (eoSignature a b x : ℂ) =
        star ((c : ℂ)⁻¹ * (eoSignature a b (fun i => !(x i)) : ℂ)) := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  have hbb : star (b : ℂ) ≠ 0 := star_ne_zero.mpr hbC
  have hab : (a : ℂ) * star (a : ℂ) = (b : ℂ) * star (b : ℂ) := by
    have h₁ : (a : ℂ) * star (a : ℂ) = (‖(a : ℂ)‖ ^ 2 : ℂ) := Complex.mul_conj' _
    have h₂ : (b : ℂ) * star (b : ℂ) = (‖(b : ℂ)‖ ^ 2 : ℂ) := Complex.mul_conj' _
    rw [h₁, h₂, hnorm]
  apply algebraic_ars_of_phase (eoSignature a b) (eoSignature_ne_zero_left a b ha)
    ((a : ℂ) / star (b : ℂ))
  intro x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [eoSignature, matrixSignature, eoMatrix, h0, h1]
  · exact (div_mul_cancel₀ _ hbb).symm
  · change (b : ℂ) = (a : ℂ) / star (b : ℂ) * star (a : ℂ)
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff hbb).mpr hab.symm

/-- The checked safe branch of the source binary argument. -/
theorem eo_finite_order_ars (a b : AlgebraicComplex) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ProjectivelyFinite (transfer (eoMatrix a b))) :
    ∃ c : AlgebraicComplex, c ≠ 0 ∧ ∀ x,
      (c : ℂ)⁻¹ * (eoSignature a b x : ℂ) =
        star ((c : ℂ)⁻¹ * (eoSignature a b (fun i => !(x i)) : ℂ)) :=
  eo_binary_algebraic_ars a b ha hb (eo_projectivelyFinite_norm a b h)

end Paper2.RelativeEO
