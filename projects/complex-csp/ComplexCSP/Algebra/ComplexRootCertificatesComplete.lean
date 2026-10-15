import ComplexCSP.Algebra.ComplexRootCertificatesContinuity

/-!
# Completeness of rational complex-root certificates at simple roots

The proof first chooses a small rational radius at the exact simple root.
Strict inequalities then remain valid in an open neighborhood of the center;
Gaussian-rational density supplies a runtime center in that neighborhood.
The same center simultaneously certifies any finite family of coordinate images
strictly inside their prescribed rational rectangles.
-/

namespace ComplexCSP.ComplexRootCertificates

open Polynomial GaussianRational Filter
open scoped Topology

 theorem isOpen_realRootGood_center {n : ℕ} (a : Code n) (r : ℝ) :
    IsOpen {c : ℂ | RealRootGood a c r} := by
  simp only [RealRootGood, Set.setOf_and]
  exact (isOpen_lt (by fun_prop) (by fun_prop)).inter
    ((isOpen_lt (by fun_prop) (by fun_prop)).inter
      (isOpen_lt (by fun_prop) (by fun_prop)))

theorem isOpen_realImageGood {n : ℕ} (a : Code n) (box : Rectangle) :
    IsOpen {p : ℂ × ℝ | RealImageGood a p.1 p.2 box} := by
  simp only [RealImageGood, Set.setOf_and]
  exact (isOpen_lt (by fun_prop) (by fun_prop)).inter
    ((isOpen_lt (by fun_prop) (by fun_prop)).inter
      ((isOpen_lt (by fun_prop) (by fun_prop)).inter
        (isOpen_lt (by fun_prop) (by fun_prop))))

/-- Arbitrarily small rational certificates exist around every simple root,
with simultaneous strict rational image-rectangle certificates. -/
theorem exists_certificates_of_simple_root
    {n : ℕ} (a : Code n) (α : ℂ) (hroot : (denote a).eval α = 0)
    (hsimple : (denote a).derivative.eval α ≠ 0)
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (q : ∀ i, Code (m i))
    (box : ι → Rectangle) (hbox : ∀ i, (box i).Contains ((denote (q i)).eval α))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : GaussianRational) (r : ℚ), 0 < r ∧ (r:ℝ) < ε ∧
      ‖toComplex c - α‖ < (r:ℝ) ∧ rootCertificate a c r = true ∧
      ∀ i, imageCertificate (q i) c r (box i) = true := by
  have hL : 0 < realDerivativeLower a α := by
    apply complexLower_pos
    simpa using hsimple
  have hzero : complexUpper (complexTaylor a α 0) = 0 := by
    simp [hroot, complexUpper]
  have hBnear : ∀ᶠ r : ℝ in 𝓝 0,
      realRemainderBound a α r < realDerivativeLower a α :=
    ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hL)
  have himages : ∀ᶠ r : ℝ in 𝓝 0, ∀ i, RealImageGood (q i) α r (box i) := by
    apply Filter.eventually_all.mpr
    intro i
    have hmem : (α,(0:ℝ)) ∈ {p : ℂ × ℝ | RealImageGood (q i) p.1 p.2 (box i)} := by
      simpa [RealImageGood, Rectangle.Contains] using hbox i
    have hcont : ContinuousAt (fun r : ℝ ↦ (α,r)) 0 := by fun_prop
    exact hcont.tendsto.eventually ((isOpen_realImageGood (q i) (box i)).eventually_mem hmem)
  obtain ⟨η,hη,hηspec⟩ := Metric.eventually_nhds_iff.mp (hBnear.and himages)
  obtain ⟨r,hr0,hrsmall⟩ := exists_rat_btwn (show (0:ℝ) < min η ε from lt_min hη hε)
  have hr : 0 < r := by exact_mod_cast hr0
  have hrη : (r:ℝ) < η := hrsmall.trans_le (min_le_left _ _)
  have hrε : (r:ℝ) < ε := hrsmall.trans_le (min_le_right _ _)
  have hrad := hηspec (y := (r:ℝ)) (by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hr0]
    exact hrη)
  have hgood : RealRootGood a α (r:ℝ) := by
    refine ⟨hL, hrad.1, ?_⟩
    rw [hzero, zero_add]
    exact mul_lt_mul_of_pos_right hrad.1 hr0
  have hrootnear : ∀ᶠ c : ℂ in 𝓝 α, RealRootGood a c (r:ℝ) :=
    (isOpen_realRootGood_center a (r:ℝ)).eventually_mem hgood
  have himagesnear : ∀ᶠ c : ℂ in 𝓝 α, ∀ i, RealImageGood (q i) c (r:ℝ) (box i) := by
    apply Filter.eventually_all.mpr
    intro i
    have hcont : ContinuousAt (fun c : ℂ ↦ (c,(r:ℝ))) α := by fun_prop
    exact hcont.tendsto.eventually
      ((isOpen_realImageGood (q i) (box i)).eventually_mem (hrad.2 i))
  obtain ⟨δ,hδ,hδspec⟩ := Metric.eventually_nhds_iff.mp (hrootnear.and himagesnear)
  obtain ⟨c,hc⟩ := GaussianRational.exists_near α (lt_min hδ hr0)
  have hcδ : dist (toComplex c) α < δ := by
    rw [dist_eq_norm]
    exact hc.trans_le (min_le_left _ _)
  have hcr : ‖toComplex c-α‖ < (r:ℝ) := hc.trans_le (min_le_right _ _)
  have hcgood := hδspec hcδ
  exact ⟨c,r,hr,hrε,hcr,(realRootGood_rational_iff a c r hr).mp hcgood.1,
    fun i ↦ (realImageGood_rational_iff (q i) c r hr.le (box i)).mp (hcgood.2 i)⟩

end ComplexCSP.ComplexRootCertificates
