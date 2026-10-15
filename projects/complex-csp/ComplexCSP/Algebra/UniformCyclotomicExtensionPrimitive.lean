import ComplexCSP.Algebra.IntegralPrimitivePresentation

/-!
# Explicit primitive combinations for uniform cyclotomic extensions

The first proof refines mathlib's `Field.primitive_element_inf_aux` by retaining
its actual rational coefficient. The adapted proof follows Thomas Browning and
Patrick Lutz's proof in Mathlib/FieldTheory/PrimitiveElement.lean (Apache 2.0).
-/
namespace ComplexCSP.AlgebraicEncoding

open Module Polynomial IntermediateField

theorem exists_primitive_linear_combination
    {F E : Type*} [Field F] [Infinite F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] (α β : E) :
    ∃ c : F, F⟮α, β⟯ = F⟮α + c • β⟯ := by
  classical
  have hα := Algebra.IsSeparable.isIntegral F α
  have hβ := Algebra.IsSeparable.isIntegral F β
  let f := minpoly F α
  let g := minpoly F β
  let ιFE := algebraMap F E
  let ιEE' := algebraMap E (SplittingField (g.map ιFE))
  obtain ⟨c, hc⟩ := Field.primitive_element_inf_aux_exists_c (ιEE'.comp ιFE) (ιEE' α) (ιEE' β) f g
  let γ := α + c • β
  suffices β_in_Fγ : β ∈ F⟮γ⟯ by
    use c
    apply le_antisymm
    · rw [adjoin_le_iff]
      have α_in_Fγ : α ∈ F⟮γ⟯ := by
        rw [← add_sub_cancel_right α (c • β)]
        exact F⟮γ⟯.sub_mem (mem_adjoin_simple_self F γ) (F⟮γ⟯.toSubalgebra.smul_mem β_in_Fγ c)
      rintro x (rfl | rfl) <;> assumption
    · rw [adjoin_simple_le_iff]
      have α_in_Fαβ : α ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert α {β})
      have β_in_Fαβ : β ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert_of_mem α rfl)
      exact F⟮α, β⟯.add_mem α_in_Fαβ (F⟮α, β⟯.smul_mem β_in_Fαβ)
  classical
  let p := EuclideanDomain.gcd ((f.map (algebraMap F F⟮γ⟯)).comp
    (C (AdjoinSimple.gen F γ) - (C ↑c : F⟮γ⟯[X]) * X)) (g.map (algebraMap F F⟮γ⟯))
  let h := EuclideanDomain.gcd ((f.map ιFE).comp (C γ - C (ιFE c) * X)) (g.map ιFE)
  have map_g_ne_zero : g.map ιFE ≠ 0 := map_ne_zero (minpoly.ne_zero hβ)
  have h_ne_zero : h ≠ 0 :=
    mt EuclideanDomain.gcd_eq_zero_iff.mp (not_and.mpr fun _ => map_g_ne_zero)
  suffices p_linear : p.map (algebraMap F⟮γ⟯ E) = C h.leadingCoeff * (X - C β) by
    have finale : β = algebraMap F⟮γ⟯ E (-p.coeff 0 / p.coeff 1) := by
      simp [map_div₀, RingHom.map_neg, ← coeff_map, ← coeff_map, p_linear,
        mul_sub, coeff_C, mul_div_cancel_left₀ β (mt leadingCoeff_eq_zero.mp h_ne_zero)]
    rw [finale]
    exact Subtype.mem (-p.coeff 0 / p.coeff 1)
  have h_sep : h.Separable := separable_gcd_right _ (.map (Algebra.IsSeparable.isSeparable F β))
  have h_root : h.eval β = 0 := by
    apply eval_gcd_eq_zero
    · rw [eval_comp, eval_sub, eval_mul, eval_C, eval_C, eval_X, eval_map, ← aeval_def, ←
        Algebra.smul_def, add_sub_cancel_right, minpoly.aeval]
    · rw [eval_map, ← aeval_def, minpoly.aeval]
  have h_splits : Splits (h.map ιEE') := by
    rw [← Polynomial.gcd_map]
    exact (SplittingField.splits _).of_dvd (map_ne_zero map_g_ne_zero)
      (EuclideanDomain.gcd_dvd_right _ _)
  have h_roots : ∀ x ∈ (h.map ιEE').roots, x = ιEE' β := by
    intro x hx
    rw [mem_roots_map h_ne_zero] at hx
    specialize hc (ιEE' γ - ιEE' (ιFE c) * x) (by
      have f_root := root_left_of_root_gcd hx
      rw [eval₂_comp, eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, eval₂_map] at f_root
      exact (mem_roots_map (minpoly.ne_zero hα)).mpr f_root)
    specialize hc x (by
      rw [mem_roots_map (minpoly.ne_zero hβ), ← eval₂_map]
      exact root_right_of_root_gcd hx)
    by_contra a
    apply hc
    apply (div_eq_iff (sub_ne_zero.mpr a)).mpr
    simp only [γ, Algebra.smul_def, RingHom.map_add, RingHom.map_mul, RingHom.comp_apply]
    ring
  rw [← eq_X_sub_C_of_separable_of_root_eq h_sep h_root h_splits h_roots]
  trans EuclideanDomain.gcd (?_ : E[X]) (?_ : E[X])
  · dsimp only [γ]
    convert (gcd_map (algebraMap F⟮γ⟯ E)).symm
  · simp only [map_comp, Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.map_sub,
      map_C, AdjoinSimple.algebraMap_gen, Polynomial.map_mul, map_X]
    congr

/-- Clearing the rational coefficient yields a positive integer coefficient on
`α` and an integer coefficient on `β`, preserving the generated field. -/
theorem exists_integral_primitive_combination
    {E : Type*} [Field E] [NumberField E] (α β : E)
    (hα : IsIntegral ℤ α) (hβ : IsIntegral ℤ β) :
    ∃ (d : ℕ) (m : ℤ), 0 < d ∧
      IsIntegral ℤ ((d : E) * α + (m : E) * β) ∧
      ℚ⟮α, β⟯ = ℚ⟮(d : E) * α + (m : E) * β⟯ := by
  obtain ⟨c, hc⟩ := exists_primitive_linear_combination (F := ℚ) α β
  have hden : (c.den : E) ≠ 0 := Nat.cast_ne_zero.mpr c.den_nz
  have he : (c.den : E) * (α + c • β) =
      (c.den : E) * α + (c.num : E) * β := by
    rw [Algebra.smul_def]
    change (c.den : E) * (α + (c : E) * β) = _
    rw [Rat.cast_def]
    field_simp
  refine ⟨c.den, c.num, c.den_pos, ?_, ?_⟩
  · apply IsIntegral.add
    · simpa only [zsmul_eq_mul, Int.cast_natCast] using
        (IsIntegral.smul (c.den : ℤ) hα)
    · simpa only [zsmul_eq_mul] using (IsIntegral.smul c.num hβ)
  · rw [← he]
    exact hc.trans (by
      simpa only [Rat.cast_natCast] using
        (adjoin_rat_mul (α + c • β) (c.den : ℚ)
          (Nat.cast_ne_zero.mpr c.den_nz)).symm)

end ComplexCSP.AlgebraicEncoding
