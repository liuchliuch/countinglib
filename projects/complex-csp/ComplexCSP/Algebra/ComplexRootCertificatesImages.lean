import ComplexCSP.Algebra.ComplexRootCertificates

/-! # Rational rectangle certificates for polynomial images of complex disks -/

namespace ComplexCSP.ComplexRootCertificates

open GaussianRational
open scoped BigOperators

structure Rectangle where
  reLo : ℚ
  reHi : ℚ
  imLo : ℚ
  imHi : ℚ
  deriving DecidableEq, Repr

/-- A literal four-rational encoding, independent of semantic complex data. -/
def Rectangle.dataEquiv : Rectangle ≃ (ℚ × ℚ × ℚ × ℚ) where
  toFun b := (b.reLo,b.reHi,b.imLo,b.imHi)
  invFun v := ⟨v.1,v.2.1,v.2.2.1,v.2.2.2⟩
  left_inv b := by cases b; rfl
  right_inv v := by rcases v with ⟨a,b,c,d⟩; rfl

instance : Encodable Rectangle := Encodable.ofEquiv _ Rectangle.dataEquiv

/-- Strict inclusion in the supplied rational rectangle. -/
def Rectangle.Contains (box : Rectangle) (z : ℂ) : Prop :=
  (box.reLo : ℝ) < z.re ∧ z.re < (box.reHi : ℝ) ∧
  (box.imLo : ℝ) < z.im ∧ z.im < (box.imHi : ℝ)

/-- A rational upper bound for variation of a coordinate polynomial on a disk. -/
def imageRadius {n : ℕ} (a : Code n) (c : GaussianRational) (r : ℚ) : ℚ :=
  upper (taylorCoefficient a c 1)*r +
    ∑ j : Fin n, upper (taylorCoefficient a c (j.val+2))*r^(j.val+2)

def imageCertificate {n : ℕ} (a : Code n) (c : GaussianRational)
    (r : ℚ) (box : Rectangle) : Bool :=
  let v := taylorCoefficient a c 0
  let R := imageRadius a c r
  decide (0 ≤ r ∧ box.reLo < v.re-R ∧ v.re+R < box.reHi ∧
    box.imLo < v.im-R ∧ v.im+R < box.imHi)

theorem imageRadius_nonneg {n : ℕ} (a : Code n) (c : GaussianRational)
    (r : ℚ) (hr : 0 ≤ r) : 0 ≤ imageRadius a c r := by
  unfold imageRadius
  apply add_nonneg (mul_nonneg (upper_nonneg _) hr)
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (upper_nonneg _) (pow_nonneg hr _)

theorem imageRadius_bound {n : ℕ} (a : Code n) (c : GaussianRational)
    (r : ℚ) (_hr : 0 ≤ r) (z : ℂ) (hz : ‖z-toComplex c‖ ≤ (r:ℝ)) :
    ‖(denote a).eval z - toComplex (taylorCoefficient a c 0)‖ ≤ (imageRadius a c r : ℝ) := by
  have he := eval_eq_taylor a c (z-toComplex c)
  rw [sub_add_cancel] at he
  rw [he]
  have hid : toComplex (taylorCoefficient a c 0) +
      toComplex (taylorCoefficient a c 1)*(z-toComplex c) +
      tailEval (fun j : Fin n ↦ toComplex (taylorCoefficient a c (j.val+2))) (z-toComplex c) -
      toComplex (taylorCoefficient a c 0) =
      toComplex (taylorCoefficient a c 1)*(z-toComplex c) +
      tailEval (fun j : Fin n ↦ toComplex (taylorCoefficient a c (j.val+2))) (z-toComplex c) := by ring
  rw [hid]
  calc
    _ ≤ ‖toComplex (taylorCoefficient a c 1)‖*‖z-toComplex c‖ +
        ∑ j : Fin n, ‖toComplex (taylorCoefficient a c (j.val+2))‖ *
          ‖z-toComplex c‖^(j.val+2) := by
      apply (norm_add_le _ _).trans
      gcongr
      · rw [norm_mul]
      · simpa only [tailEval, norm_mul, norm_pow] using
          norm_sum_le Finset.univ (fun j : Fin n ↦
            toComplex (taylorCoefficient a c (j.val+2))*(z-toComplex c)^(j.val+2))
    _ ≤ (upper (taylorCoefficient a c 1) : ℝ)*(r:ℝ) +
        ∑ j : Fin n, (upper (taylorCoefficient a c (j.val+2)) : ℝ)*(r:ℝ)^(j.val+2) := by
      gcongr
      all_goals first | exact norm_le_upper _ | exact_mod_cast upper_nonneg _
    _ = _ := by simp [imageRadius]

/-- Every point of the entire disk, hence its certified root, has its image in
the rectangle accepted by the finite rational checker. -/
theorem imageCertificate_sound {n : ℕ} (a : Code n) (c : GaussianRational)
    (r : ℚ) (box : Rectangle) (h : imageCertificate a c r box = true)
    (z : ℂ) (hz : ‖z-toComplex c‖ ≤ (r:ℝ)) : box.Contains ((denote a).eval z) := by
  simp only [imageCertificate, decide_eq_true_eq] at h
  obtain ⟨hr,hre₁,hre₂,him₁,him₂⟩ := h
  have hnorm := imageRadius_bound a c r hr z hz
  have hre := (Complex.abs_re_le_norm _).trans hnorm
  have him := (Complex.abs_im_le_norm _).trans hnorm
  simp only [Complex.sub_re, Complex.sub_im, toComplex_re, toComplex_im] at hre him
  have hre' := abs_le.mp hre
  have him' := abs_le.mp him
  have hr₁ : (box.reLo:ℝ) < (taylorCoefficient a c 0).re - (imageRadius a c r : ℝ) :=
    by exact_mod_cast hre₁
  have hr₂ : ((taylorCoefficient a c 0).re:ℝ) + (imageRadius a c r:ℝ) < box.reHi :=
    by exact_mod_cast hre₂
  have hi₁ : (box.imLo:ℝ) < (taylorCoefficient a c 0).im - (imageRadius a c r:ℝ) :=
    by exact_mod_cast him₁
  have hi₂ : ((taylorCoefficient a c 0).im:ℝ) + (imageRadius a c r:ℝ) < box.imHi :=
    by exact_mod_cast him₂
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end ComplexCSP.ComplexRootCertificates
