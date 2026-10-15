import ComplexCSP.Algebra.Purification

/-!
# Algebraic soundness of degenerate certificate groups

These finite-algebra results cover support propagation by twisted minors and
preservation of zero Hermitian sums when certified groups disappear or merge.
The finite certificate family and the legal purification construction are
separate developments.
-/

namespace ComplexCSP.CertificateAlgebra

open scoped BigOperators
open BlockOrthogonality

/-- A twisted minor with a common nonzero anchor propagates zero positions,
even if arbitrary other certified coordinates have specialized to zero. -/
theorem support_eq_of_twisted_minors {D K : Type*} [Field K]
    (u v τ : D → K) (e : D) (hue : u e ≠ 0) (hve : v e ≠ 0)
    (hτ : ∀ z, τ z ≠ 0)
    (hminor : ∀ z, u z * v e = τ z * (u e * v z)) :
    ∀ z, u z = 0 ↔ v z = 0 := by
  intro z
  have h := congrArg (fun x : K ↦ x = 0) (hminor z)
  simpa only [mul_eq_zero, hτ z, hue, hve, false_or, or_false] using iff_of_eq h

/-- Vanishing fiber sums still vanish on any union of whole fibers. This is the
finite partition-merge step of certificate soundness. -/
theorem sum_filter_eq_zero_of_fibers {D J K : Type*}
    [Fintype D] [Fintype J] [DecidableEq J] [AddCommMonoid K]
    (block : D → J) (f : D → K) (p : D → Prop) [DecidablePred p]
    (hconstant : ∀ z w, block z = block w → (p z ↔ p w))
    (hzero : ∀ j, (∑ z ∈ Finset.univ.filter (fun z ↦ block z = j), f z) = 0) :
    (∑ z ∈ Finset.univ.filter p, f z) = 0 := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ.filter p) block]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hex : ∃ z, block z = j ∧ p z
  · obtain ⟨w, hw, hpw⟩ := hex
    have hfilter : (Finset.univ.filter p).filter (fun z ↦ block z = j) =
        Finset.univ.filter (fun z ↦ block z = j) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact And.right
      · intro hz
        exact ⟨(hconstant z w (hz.trans hw.symm)).mpr hpw, hz⟩
    rw [hfilter, hzero j]
  · have hfilter : (Finset.univ.filter p).filter (fun z ↦ block z = j) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact hex ⟨z, hz'.2, (Finset.mem_filter.mp hz'.1).2⟩
    simp [hfilter]

/-- Anchor equations factor the whole Hermitian sum on a certified group,
including the case of a zero anchor. -/
theorem hermitianSum_eq_anchor_mul_rootSum {D : Type*}
    (u v ρ σ : D → ℂ) (B : Finset D) (a b : ℂ)
    (hu : ∀ z ∈ B, u z = ρ z * a)
    (hv : ∀ z ∈ B, v z = σ z * b) :
    hermitianSum u v B = (a * star b) * ∑ z ∈ B, ρ z * star (σ z) := by
  unfold hermitianSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [hu z hz, hv z hz, star_mul]
  ring

/-- A zero root sum makes an entire certified group orthogonal, without any
nonzero-entry hypothesis. Thus disappearing groups are covered automatically. -/
theorem hermitianSum_eq_zero_of_anchors {D : Type*}
    (u v ρ σ : D → ℂ) (B : Finset D) (a b : ℂ)
    (hu : ∀ z ∈ B, u z = ρ z * a)
    (hv : ∀ z ∈ B, v z = σ z * b)
    (hsum : (∑ z ∈ B, ρ z * star (σ z)) = 0) : hermitianSum u v B = 0 := by
  rw [hermitianSum_eq_anchor_mul_rootSum u v ρ σ B a b hu hv, hsum, mul_zero]

/-- Root-valued anchor equations keep the norm constant on a whole certified
fiber. No surviving certified group can split into separate magnitude levels. -/
theorem norm_eq_of_same_anchor_group {D J : Type*} (u ρ : D → ℂ)
    (block : D → J) (a : J → ℂ)
    (hu : ∀ z, u z = ρ z * a (block z)) (hρ : ∀ z, ‖ρ z‖ = 1)
    {z w : D} (hzw : block z = block w) : ‖u z‖ = ‖u w‖ := by
  rw [hu z, hu w, norm_mul, norm_mul, hρ z, hρ w, one_mul, one_mul, hzw]

/-- All anchor-certified groups may vanish or merge, but the resulting row pair
remains block-orthogonal. This is the orthogonal-mode degeneration argument in
Section 4.2, stated directly for the purified rows. -/
theorem vectorBlockOrthogonal_of_anchor_groups {D J : Type*}
    [Fintype D] [Fintype J] [DecidableEq J]
    (u v ρ σ : D → ℂ) (block : D → J) (a b : J → ℂ)
    (hu : ∀ z, u z = ρ z * a (block z))
    (hv : ∀ z, v z = σ z * b (block z))
    (hρ : ∀ z, ‖ρ z‖ = 1)
    (hroot : ∀ j, (∑ z ∈ Finset.univ.filter (fun z ↦ block z = j),
      ρ z * star (σ z)) = 0) : VectorBlockOrthogonal u v := by
  classical
  intro w _
  apply sum_filter_eq_zero_of_fibers block (fun z ↦ u z * star (v z))
    (fun z ↦ ‖u z‖ = ‖u w‖)
  · intro z z' hzz'
    rw [norm_eq_of_same_anchor_group u ρ block a hu hρ hzz']
  · intro j
    exact hermitianSum_eq_zero_of_anchors u v ρ σ _ (a j) (b j)
      (fun z hz ↦ by rw [hu z, (Finset.mem_filter.mp hz).2])
      (fun z hz ↦ by rw [hv z, (Finset.mem_filter.mp hz).2]) (hroot j)

/-- A norm-constant finite partition with zero Hermitian sum on every fiber
remains orthogonal after all equal-norm fibers are merged. -/
theorem vectorBlockOrthogonal_of_fiber_sums {D J : Type*}
    [Fintype D] [Fintype J] [DecidableEq J]
    (u v : D → ℂ) (block : D → J)
    (hnorm : ∀ z w, block z = block w → ‖u z‖ = ‖u w‖)
    (hzero : ∀ j, (∑ z ∈ Finset.univ.filter (fun z ↦ block z = j),
      u z * star (v z)) = 0) : VectorBlockOrthogonal u v := by
  classical
  intro w _
  apply sum_filter_eq_zero_of_fibers block (fun z ↦ u z * star (v z))
    (fun z ↦ ‖u z‖ = ‖u w‖)
  · intro z z' hzz'
    rw [hnorm z z' hzz']
  · exact hzero

end ComplexCSP.CertificateAlgebra
