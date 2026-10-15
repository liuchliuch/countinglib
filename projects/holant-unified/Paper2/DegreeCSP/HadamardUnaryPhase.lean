import Paper2.DegreeCSP.BinaryPhaseChart

/-! An actual unary coefficient pair and its Hadamard Fourier pair. Original
row and column block orthogonality forces a fourth-root ratio, including the
two Fourier pairs with a zero entry. -/
namespace Paper2.DegreeCSP.HadamardUnaryPhase
open OriginalBO
noncomputable section
set_option maxHeartbeats 600000

def table (a b : ℂ) (x y : Bool) : ℂ :=
  (if x then b else a)*(if x&&y then -1 else 1)

theorem table_nonzero (a b : ℂ) (ha : a≠0) (hb : b≠0) :
    ∀ x y,table a b x y≠0 := by
  intro x y
  cases x <;> cases y <;> simp [table,ha,hb]

theorem table_determinant (a b : ℂ) : binaryDeterminant (table a b) = -2*a*b := by
  simp [table,binaryDeterminant]
  ring

theorem equal_magnitudes (a b : ℂ) (ha : a≠0) (hb : b≠0)
    (h : BlockOrthogonal (table a b))
    (ht : BlockOrthogonal (fun x y => table a b y x)) : ‖a‖=‖b‖ := by
  have hd : binaryDeterminant (table a b)≠0 := by
    rw [table_determinant]
    exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hb
  have hm := nonzero_determinant_equal_magnitudes (table a b)
    (table_nonzero a b ha hb) h ht hd true false
  simpa [table] using hm.symm

private theorem star_norm (a : ℂ) : star a*a=(‖a‖ : ℂ)^2 :=
  Complex.conj_mul' a

theorem unit_imaginary_ratio (a b : ℂ) (ha : a≠0)
    (hmag : ‖a‖=‖b‖) (hfourier : ‖a+b‖=‖a-b‖) : (b/a)^2 = -1 := by
  have hn : star a*a=star b*b := by rw [star_norm,star_norm,hmag]
  have hf : star (a+b)*(a+b)=star (a-b)*(a-b) := by
    rw [star_norm,star_norm,hfourier]
  simp only [star_add,star_sub] at hf
  have ho : a*star b+b*star a=0 := by
    have hv : (2 : ℂ)*(a*star b+b*star a)=0 := by linear_combination hf
    exact (mul_eq_zero.mp hv).resolve_left (by norm_num)
  have hv : (a^2+b^2)*star a=0 := by
    calc
      _=a*(star a*a)+b^2*star a := by ring
      _=a*(star b*b)+b^2*star a := by rw [hn]
      _=b*(a*star b+b*star a) := by ring
      _=0 := by rw [ho,mul_zero]
  have hs : a^2+b^2=0 :=
    (mul_eq_zero.mp hv).resolve_right (star_ne_zero.mpr ha)
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 2 ha)).mpr
  linear_combination hs

/-- Every supplied BO premise is about the literal original complex table.
The two Fourier zero cases yield ratios -1 and 1, respectively. -/
theorem phase_four (a b : ℂ) (ha : a≠0) (hb : b≠0)
    (h : BlockOrthogonal (table a b))
    (ht : BlockOrthogonal (fun x y => table a b y x))
    (hw : BlockOrthogonal (table (a+b) (a-b)))
    (hwt : BlockOrthogonal (fun x y => table (a+b) (a-b) y x)) : (b/a)^4=1 := by
  by_cases hplus : a+b=0
  · have he : b= -a := by linear_combination hplus
    rw [he,neg_div,div_self ha]
    norm_num
  by_cases hminus : a-b=0
  · have he : b=a := (sub_eq_zero.mp hminus).symm
    rw [he,div_self ha]
    norm_num
  have hm := equal_magnitudes a b ha hb h ht
  have hwm := equal_magnitudes (a+b) (a-b) hplus hminus hw hwt
  have hs := unit_imaginary_ratio a b ha hm hwm
  calc
    (b/a)^4=((b/a)^2)^2 := by ring
    _=1 := by rw [hs]; norm_num

end
end Paper2.DegreeCSP.HadamardUnaryPhase
