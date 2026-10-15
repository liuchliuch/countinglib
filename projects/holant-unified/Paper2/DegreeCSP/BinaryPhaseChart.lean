import Paper2.DegreeCSP.GeneratedOrthogonality
import Mathlib.Algebra.Ring.Commute

/-! A literal full binary table under original block orthogonality. The
non-rank-one alternative has the signed binary chart with two explicit
unit phases. This local result imposes no shared phase across a family. -/
namespace Paper2.DegreeCSP.OriginalBO
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 500000

def binaryDeterminant (G : Bool → Bool → ℂ) : ℂ :=
  G false false*G true true-G false true*G true false

/-- The nonzero block containing a Boolean coordinate cannot be a singleton. -/
theorem boolean_equal_magnitudes (u v : Bool → ℂ)
    (hu : ∀ j,u j≠0) (hv : ∀ j,v j≠0)
    (h : VectorBlockOrthogonal u v) : ‖u false‖=‖u true‖ := by
  classical
  by_contra ne
  have h0 := h false (hu false)
  have zero : u false*star (v false)=0 := by
    simpa [hermitianSum,magnitudeBlock,Finset.sum_filter,Fintype.sum_bool,
      ne,Ne.symm ne] using h0
  exact (mul_ne_zero (hu false) (star_ne_zero.mpr (hv false))) zero

theorem proportional_determinant (G : Bool → Bool → ℂ)
    (h : Proportional (G false) (G true)) : binaryDeterminant G=0 := by
  obtain ⟨c,hc,equation⟩ := h
  simp only [binaryDeterminant,equation false,equation true]
  ring

theorem nonzero_determinant_row_orthogonal (G : Bool → Bool → ℂ)
    (hne : ∀ i j,G i j≠0) (h : BlockOrthogonal G)
    (hd : binaryDeterminant G≠0) : VectorBlockOrthogonal (G false) (G true) := by
  have rows (i : Bool) : G i≠0 := fun hz => hne i false (congrFun hz false)
  have magnitudes : MagnitudeProportional (G false) (G true) := by
    rcases h.1 false true (rows false) (rows true) with proportional|disjoint
    · exact proportional
    · exact False.elim
        (Set.disjoint_left.mp disjoint (hne false false) (hne true false))
  rcases h.2 false true (rows false) (rows true) magnitudes with proportional|orthogonal
  · exact False.elim (hd (proportional_determinant G proportional))
  · exact orthogonal

/-- Row and column BO give one common positive coefficient magnitude in the
non-rank-one alternative. The row-square assumption is not needed here. -/
theorem nonzero_determinant_equal_magnitudes (G : Bool → Bool → ℂ)
    (hne : ∀ i j,G i j≠0) (h : BlockOrthogonal G)
    (ht : BlockOrthogonal (fun i j => G j i))
    (hd : binaryDeterminant G≠0) : ∀ i j,‖G i j‖=‖G false false‖ := by
  have transposeDet : binaryDeterminant (fun i j => G j i)=binaryDeterminant G := by
    simp only [binaryDeterminant]
    ring
  have row := boolean_equal_magnitudes (G false) (G true) (hne false) (hne true)
    (nonzero_determinant_row_orthogonal G hne h hd)
  have col := boolean_equal_magnitudes (fun i => G i false) (fun i => G i true)
    (fun i => hne i false) (fun i => hne i true)
    (nonzero_determinant_row_orthogonal (fun i j => G j i) (fun i j => hne j i) ht
      (transposeDet ▸ hd))
  have other := boolean_equal_magnitudes (G true) (G false) (hne true) (hne false) (by
    have switched : BlockOrthogonal (fun i j => G (!i) j) := precompose_rows h Bool.not
    have switchedDet : binaryDeterminant (fun i j => G (!i) j)=-binaryDeterminant G := by
      simp only [binaryDeterminant,Bool.not_false,Bool.not_true]
      ring
    exact nonzero_determinant_row_orthogonal _ (fun i j => hne (!i) j) switched
      (switchedDet ▸ neg_ne_zero.mpr hd))
  intro i j
  cases i <;> cases j
  · rfl
  · exact row.symm
  · exact col.symm
  · exact other.symm.trans col.symm

def firstPhase (G : Bool → Bool → ℂ) : ℂ := G true false/G false false
def secondPhase (G : Bool → Bool → ℂ) : ℂ := G false true/G false false

/-- This equals a u^b v^c (-1)^(b∧c), with Boolean exponents. -/
def phaseChart (a u v : ℂ) (b c : Bool) : ℂ :=
  a*(if b then u else 1)*(if c then v else 1)*(if b&&c then -1 else 1)

theorem negative_cross_chart (G : Bool → Bool → ℂ)
    (ha : G false false≠0)
    (negative : G false false*G true true= -(G false true*G true false)) :
    ∀ b c,G b c=phaseChart (G false false) (firstPhase G) (secondPhase G) b c := by
  intro b c
  cases b <;> cases c
  · simp [phaseChart]
  · simp only [phaseChart,secondPhase,Bool.false_eq_true,ite_false,ite_true,
      Bool.false_and,mul_one]
    field_simp
  · simp only [phaseChart,firstPhase,Bool.false_eq_true,ite_false,ite_true,
      Bool.and_false,mul_one]
    field_simp
  · simp only [phaseChart,firstPhase,secondPhase,ite_true,Bool.and_self]
    field_simp
    linear_combination negative

/-- BO of the original full table, its actual square, and its transpose
gives rank one or the exact signed chart with two independent unit phases. -/
theorem binary_phase_alternative (G : Bool → Bool → ℂ)
    (hne : ∀ i j,G i j≠0) (h : BlockOrthogonal G)
    (h2 : BlockOrthogonal (fun i j => G i j^2))
    (ht : BlockOrthogonal (fun i j => G j i)) :
    binaryDeterminant G=0 ∨
      (G false false*G true true= -(G false true*G true false) ∧
        (∀ i j,‖G i j‖=‖G false false‖) ∧
        firstPhase G≠0 ∧ secondPhase G≠0 ∧
        ‖firstPhase G‖=1 ∧ ‖secondPhase G‖=1 ∧
        ∀ b c,G b c=phaseChart (G false false) (firstPhase G) (secondPhase G) b c) := by
  by_cases determinant : binaryDeterminant G=0
  · exact Or.inl determinant
  right
  have negative : G false false*G true true= -(G false true*G true false) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (binary_squared_cross G hne h h2) with equal|negative
    · exact False.elim (determinant (sub_eq_zero.mpr equal))
    · exact negative
  have magnitudes := nonzero_determinant_equal_magnitudes G hne h ht determinant
  have haNorm : ‖G false false‖≠0 := norm_ne_zero_iff.mpr (hne false false)
  refine ⟨negative,magnitudes,div_ne_zero (hne true false) (hne false false),
    div_ne_zero (hne false true) (hne false false),?_,?_,
    negative_cross_chart G (hne false false) negative⟩
  · rw [firstPhase,norm_div,magnitudes true false,div_self haNorm]
  · rw [secondPhase,norm_div,magnitudes false true,div_self haNorm]

/-- The coefficient table of literal zero-pin padding, before any outer
power is taken. Physical generation is proved in PinnedBinaryPadding. -/
def pinPadded (G : Bool → Bool → ℂ) (t : ℕ) (i j : Bool) : ℂ :=
  G i j*G i false^t*G j false^t

theorem pin_padded_nonzero (G : Bool → Bool → ℂ) (t : ℕ)
    (hne : ∀ i j,G i j≠0) : ∀ i j,pinPadded G t i j≠0 := by
  intro i j
  exact mul_ne_zero (mul_ne_zero (hne i j) (pow_ne_zero t (hne i false)))
    (pow_ne_zero t (hne j false))

theorem pin_padded_determinant (G : Bool → Bool → ℂ) (t : ℕ) :
    binaryDeterminant (pinPadded G t)=
      (G false false^t*G true false^t)^2*binaryDeterminant G := by
  simp only [binaryDeterminant,pinPadded]
  ring

/-- Equal magnitudes of the genuine zero-pin-padded table reflect back to
equal magnitudes of all four original coefficients. No phase is discarded. -/
theorem pin_padded_equal_magnitudes (G : Bool → Bool → ℂ) (t : ℕ)
    (hne : ∀ i j,G i j≠0)
    (magnitudes : ∀ i j,‖pinPadded G t i j‖=‖pinPadded G t false false‖) :
    ∀ i j,‖G i j‖=‖G false false‖ := by
  let A : ℝ := ‖G false false‖
  let B : ℝ := ‖G false true‖
  let C : ℝ := ‖G true false‖
  let D : ℝ := ‖G true true‖
  have ha : A≠0 := norm_ne_zero_iff.mpr (hne false false)
  have hc : C≠0 := norm_ne_zero_iff.mpr (hne true false)
  have hat : A^t≠0 := pow_ne_zero t ha
  have hct : C^t≠0 := pow_ne_zero t hc
  have e01 : B*A^t*C^t=A*A^t*A^t := by
    simpa only [pinPadded,norm_mul,norm_pow] using magnitudes false true
  have e10 : C*C^t*A^t=A*A^t*A^t := by
    simpa only [pinPadded,norm_mul,norm_pow] using magnitudes true false
  have e11 : D*C^t*C^t=A*A^t*A^t := by
    simpa only [pinPadded,norm_mul,norm_pow] using magnitudes true true
  have bc : B=C := mul_right_cancel₀ (mul_ne_zero hat hct) (by
    calc
      B*(A^t*C^t)=B*A^t*C^t := by ring
      _=C*C^t*A^t := e01.trans e10.symm
      _=C*(A^t*C^t) := by ring)
  have powers : A^(t+1)=C^(t+1) := mul_right_cancel₀ hat (by
    calc
      A^(t+1)*A^t=A*A^t*A^t := by rw [pow_succ]; ring
      _=C*C^t*A^t := e10.symm
      _=C^(t+1)*A^t := by rw [pow_succ]; ring)
  have ac : A=C := (pow_left_inj₀ (norm_nonneg (G false false))
    (norm_nonneg (G true false)) (Nat.succ_ne_zero t)).mp powers
  have da : D=A := mul_right_cancel₀ (mul_ne_zero hat hat) (by
    simpa only [←ac,mul_assoc] using e11)
  intro i j
  cases i <;> cases j
  · rfl
  · exact bc.trans ac.symm
  · exact ac.symm
  · exact da

theorem pin_padded_negative_cross (G : Bool → Bool → ℂ) (t : ℕ)
    (hne : ∀ i j,G i j≠0)
    (negative : pinPadded G t false false*pinPadded G t true true=
      -(pinPadded G t false true*pinPadded G t true false)) :
    G false false*G true true= -(G false true*G true false) := by
  have scale : (G false false^t*G true false^t)^2≠0 :=
    pow_ne_zero 2 (mul_ne_zero (pow_ne_zero t (hne false false))
      (pow_ne_zero t (hne true false)))
  apply (mul_right_inj' scale).mp
  calc
    (G false false^t*G true false^t)^2*(G false false*G true true)=
      pinPadded G t false false*pinPadded G t true true := by
        simp only [pinPadded]
        ring
    _= -(pinPadded G t false true*pinPadded G t true false) := negative
    _= (G false false^t*G true false^t)^2*(-(G false true*G true false)) := by
        simp only [pinPadded]
        ring

/-- The original coefficients inherit the literal signed chart from BO of
the actual padded table and its square and transpose. -/
theorem binary_phase_alternative_of_pin_padding (G : Bool → Bool → ℂ) (t : ℕ)
    (hne : ∀ i j,G i j≠0) (h : BlockOrthogonal (pinPadded G t))
    (h2 : BlockOrthogonal (fun i j => pinPadded G t i j^2))
    (ht : BlockOrthogonal (fun i j => pinPadded G t j i)) :
    binaryDeterminant G=0 ∨
      (G false false*G true true= -(G false true*G true false) ∧
        (∀ i j,‖G i j‖=‖G false false‖) ∧
        firstPhase G≠0 ∧ secondPhase G≠0 ∧
        ‖firstPhase G‖=1 ∧ ‖secondPhase G‖=1 ∧
        ∀ b c,G b c=phaseChart (G false false) (firstPhase G) (secondPhase G) b c) := by
  rcases binary_phase_alternative (pinPadded G t) (pin_padded_nonzero G t hne) h h2 ht with
    determinant|⟨negative,magnitudes,_,_,_,_,_⟩
  · left
    rw [pin_padded_determinant] at determinant
    exact (mul_eq_zero.mp determinant).resolve_left
      (pow_ne_zero 2 (mul_ne_zero (pow_ne_zero t (hne false false))
        (pow_ne_zero t (hne true false))))
  · right
    have neg := pin_padded_negative_cross G t hne negative
    have mag := pin_padded_equal_magnitudes G t hne magnitudes
    have haNorm : ‖G false false‖≠0 := norm_ne_zero_iff.mpr (hne false false)
    refine ⟨neg,mag,div_ne_zero (hne true false) (hne false false),
      div_ne_zero (hne false true) (hne false false),?_,?_,
      negative_cross_chart G (hne false false) neg⟩
    · rw [firstPhase,norm_div,mag true false,div_self haNorm]
    · rw [secondPhase,norm_div,mag false true,div_self haNorm]

end
end Paper2.DegreeCSP.OriginalBO

