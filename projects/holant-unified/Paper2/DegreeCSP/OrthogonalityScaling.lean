import Paper2.DegreeCSP.BooleanOrthogonality

/-! A common nonzero scalar preserves literal original block orthogonality,
including every actual magnitude block and Hermitian sum. -/
namespace Paper2.DegreeCSP.OriginalBO
open scoped BigOperators
noncomputable section
variable {X J : Type} [Fintype J]

omit [Fintype J] in
private theorem scale_row_ne_zero (c : ℂ) (hc : c ≠ 0) (u : J → ℂ) :
    (fun j => c*u j) ≠ 0 ↔ u ≠ 0 := by
  constructor
  · intro h hz
    apply h
    funext j
    simp [hz]
  · intro h hz
    apply h
    funext j
    have he := congrFun hz j
    simpa only [Pi.zero_apply,mul_eq_zero,or_iff_right hc] using he

omit [Fintype J] in
theorem proportional_scale (c : ℂ) (hc : c ≠ 0) (u v : J → ℂ) :
    Proportional (fun j => c*u j) (fun j => c*v j) ↔ Proportional u v := by
  constructor
  · rintro ⟨a,ha,he⟩
    refine ⟨a,ha,fun j => mul_left_cancel₀ hc ?_⟩
    calc c*u j = a*(c*v j) := he j
         _ = c*(a*v j) := by ring
  · rintro ⟨a,ha,he⟩
    refine ⟨a,ha,fun j => ?_⟩
    change c*u j = a*(c*v j)
    rw [he j]
    ring

omit [Fintype J] in
theorem magnitude_proportional_scale (c : ℂ) (hc : c ≠ 0) (u v : J → ℂ) :
    MagnitudeProportional (fun j => c*u j) (fun j => c*v j) ↔
      MagnitudeProportional u v := by
  have hnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  constructor
  · rintro ⟨a,ha,he⟩
    refine ⟨a,ha,fun j => mul_left_cancel₀ hnorm ?_⟩
    calc
      ‖c‖*‖u j‖ = a*(‖c‖*‖v j‖) := by simpa only [norm_mul] using he j
      _ = ‖c‖*(a*‖v j‖) := by ring
  · rintro ⟨a,ha,he⟩
    refine ⟨a,ha,fun j => ?_⟩
    simp only [norm_mul,he j]
    ring

omit [Fintype J] in
theorem support_scale (c : ℂ) (hc : c ≠ 0) (u : J → ℂ) :
    support (fun j => c*u j) = support u := by
  ext j
  simp [support,hc]

theorem magnitude_block_scale (c : ℂ) (hc : c ≠ 0) (u : J → ℂ) (z : J) :
    magnitudeBlock (fun j => c*u j) z = magnitudeBlock u z := by
  classical
  ext j
  simp only [magnitudeBlock,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [norm_mul,norm_mul]
  exact ⟨fun h => mul_left_cancel₀ (norm_ne_zero_iff.mpr hc) h,
    fun h => congrArg (fun r : ℝ => ‖c‖*r) h⟩

omit [Fintype J] in
theorem hermitian_scale (c : ℂ) (u v : J → ℂ) (B : Finset J) :
    hermitianSum (fun j => c*u j) (fun j => c*v j) B =
      (c*star c)*hermitianSum u v B := by
  simp only [hermitianSum,star_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem vector_bo_scale (c : ℂ) (hc : c ≠ 0) (u v : J → ℂ) :
    VectorBlockOrthogonal (fun j => c*u j) (fun j => c*v j) ↔
      VectorBlockOrthogonal u v := by
  constructor
  · intro h z hz
    have he := h z (mul_ne_zero hc hz)
    rw [magnitude_block_scale c hc,hermitian_scale] at he
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hc (star_ne_zero.mpr hc))
  · intro h z hz
    have huz : u z ≠ 0 := (mul_ne_zero_iff.mp hz).2
    rw [magnitude_block_scale c hc,hermitian_scale,h z huz,mul_zero]

/-- Strip or introduce the actual common scalar of an entire row table. -/
theorem block_orthogonal_scale (c : ℂ) (hc : c ≠ 0) (G : X → J → ℂ) :
    BlockOrthogonal (fun x j => c*G x j) ↔ BlockOrthogonal G := by
  constructor
  · rintro ⟨rank,orth⟩
    constructor
    · intro x y hx hy
      rcases rank x y ((scale_row_ne_zero c hc _).mpr hx)
        ((scale_row_ne_zero c hc _).mpr hy) with mag|disjoint
      · exact Or.inl ((magnitude_proportional_scale c hc _ _).mp mag)
      · exact Or.inr (by simpa only [support_scale c hc] using disjoint)
    · intro x y hx hy hm
      rcases orth x y ((scale_row_ne_zero c hc _).mpr hx)
        ((scale_row_ne_zero c hc _).mpr hy)
        ((magnitude_proportional_scale c hc _ _).mpr hm) with prop|ortho
      · exact Or.inl ((proportional_scale c hc _ _).mp prop)
      · exact Or.inr ((vector_bo_scale c hc _ _).mp ortho)
  · rintro ⟨rank,orth⟩
    constructor
    · intro x y hx hy
      rcases rank x y ((scale_row_ne_zero c hc _).mp hx)
        ((scale_row_ne_zero c hc _).mp hy) with mag|disjoint
      · exact Or.inl ((magnitude_proportional_scale c hc _ _).mpr mag)
      · exact Or.inr (by simpa only [support_scale c hc] using disjoint)
    · intro x y hx hy hm
      rcases orth x y ((scale_row_ne_zero c hc _).mp hx)
        ((scale_row_ne_zero c hc _).mp hy)
        ((magnitude_proportional_scale c hc _ _).mp hm) with prop|ortho
      · exact Or.inl ((proportional_scale c hc _ _).mpr prop)
      · exact Or.inr ((vector_bo_scale c hc _ _).mpr ortho)

end
end Paper2.DegreeCSP.OriginalBO
