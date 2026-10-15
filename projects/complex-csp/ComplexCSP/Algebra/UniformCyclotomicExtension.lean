import ComplexCSP.Algebra.UniformCyclotomicExtensionPrimitive
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# Semantic existence of the searched cyclotomic extension

All statements here support uniform-input research. We construct the extension
mathematically from the old number field and prescribed positive root order;
no desired extension or primitive generator is supplied as an oracle.
-/
namespace ComplexCSP.AlgebraicEncoding

open Polynomial IntermediateField

/-- Primitive generators in a tower jointly generate over the bottom field. -/
theorem adjoin_pair_eq_top_of_tower
    {K E : Type*} [Field K] [CharZero K] [Field E] [CharZero E]
    [Algebra K E] [IsScalarTower ℚ K E]
    (a : K) (b : E) (ha : ℚ⟮a⟯ = ⊤) (hb : K⟮b⟯ = ⊤) :
    ℚ⟮algebraMap K E a, b⟯ = ⊤ := by
  let S : IntermediateField ℚ E := ℚ⟮algebraMap K E a, b⟯
  have hKa : algebraMap K E a ∈ S := subset_adjoin ℚ _ (by simp)
  have hEb : b ∈ S := subset_adjoin ℚ _ (by simp)
  have hK : ∀ x : K, algebraMap K E x ∈ S := by
    intro x
    have hx : x ∈ ℚ⟮a⟯ := by rw [ha]; trivial
    refine adjoin_induction ℚ ?_ ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hKa
    · intro q
      simpa only [← IsScalarTower.algebraMap_apply ℚ K E] using S.algebraMap_mem q
    · intro x y _ _ hx hy
      simpa only [map_add] using S.add_mem hx hy
    · intro x _ hx
      simpa only [map_inv₀] using S.inv_mem hx
    · intro x y _ _ hx hy
      simpa only [map_mul] using S.mul_mem hx hy
  apply top_unique
  intro x _
  have hx : x ∈ K⟮b⟯ := by rw [hb]; trivial
  refine adjoin_induction K ?_ hK ?_ ?_ ?_ hx
  · intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact hEb
  · intro x y _ _ hx hy
    exact S.add_mem hx hy
  · intro x _ hx
    exact S.inv_mem hx
  · intro x y _ _ hx hy
    exact S.mul_mem hx hy

variable (K : Type*) [Field K] [NumberField K]

/-- A concrete mathematical extension containing the prescribed root. -/
abbrev CyclotomicExtension (δ : ℕ) := CyclotomicField δ K

/-- In this extension, an integral primitive generator has exactly the form
required by the finite candidate search: `d * oldGenerator + m * root`. -/
theorem exists_cyclotomic_integral_generator (old : IntegralPrimitivePresentation K)
    (δ : ℕ) (hδ : 0 < δ) :
    ∃ (ζ : CyclotomicExtension K δ) (d : ℕ) (m : ℤ),
      IsPrimitiveRoot ζ δ ∧ 0 < d ∧
      IsIntegral ℤ ((d : CyclotomicExtension K δ) *
        algebraMap K (CyclotomicExtension K δ) old.basis.gen + (m : _) * ζ) ∧
      ℚ⟮(d : CyclotomicExtension K δ) *
        algebraMap K (CyclotomicExtension K δ) old.basis.gen + (m : _) * ζ⟯ = ⊤ := by
  letI : NeZero δ := ⟨ne_of_gt hδ⟩
  let E := CyclotomicExtension K δ
  let ζ : E := IsCyclotomicExtension.zeta δ K E
  have hζ : IsPrimitiveRoot ζ δ := IsCyclotomicExtension.zeta_spec δ K E
  have ha : ℚ⟮old.basis.gen⟯ = ⊤ :=
    adjoin_eq_top_of_algebra ℚ _ old.basis.adjoin_gen_eq_top
  have hb : K⟮ζ⟯ = ⊤ :=
    adjoin_eq_top_of_algebra K _ (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)
  have hab := adjoin_pair_eq_top_of_tower old.basis.gen ζ ha hb
  obtain ⟨d, m, hd, hi, hg⟩ := exists_integral_primitive_combination
    (algebraMap K E old.basis.gen) ζ old.integral.algebraMap (hζ.isIntegral hδ)
  exact ⟨ζ, d, m, hζ, hd, hi, hg.symm.trans hab⟩

end ComplexCSP.AlgebraicEncoding
